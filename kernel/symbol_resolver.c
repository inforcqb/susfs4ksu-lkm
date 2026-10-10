/* SPDX-License-Identifier: GPL-2.0 */

#include "symbol_resolver.h"
#include "susfs_log.h"
#include <linux/kallsyms.h>
#include <linux/kprobes.h>
#include <linux/module.h>
#include <linux/string.h>
#include <linux/version.h>

/* https://github.com/torvalds/linux/commit/89245600941e4e0f87d77f60ee269b5e61ef4e49 */
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 1, 0)
#define USE_KCFI 1
#else
#define USE_KCFI 0
#endif

#if !USE_KCFI
static const char cfi_suffix[] = ".cfi_jt";
static const size_t cfi_suffix_len = sizeof(cfi_suffix) - 1;
#endif

/* It's not guaranteed kallsyms_on_each_symbol exists in 5.x. */
#if LINUX_VERSION_CODE >= KERNEL_VERSION(5, 19, 0)
#define ALWAYS_HAVE_ON_EACH_SYMBOL 1
#else
#define ALWAYS_HAVE_ON_EACH_SYMBOL 0
#endif

/* Only used from 6.6 up, and that gate is empirical rather than a version fact: gating this path
 * at 6.1 was measured to produce a spurious "cannot bootstrap" warning on the android14-6.1
 * variant (a load-time warning, not a build one), after which the code fell back to the
 * kallsyms_lookup_name() path every other build uses anyway. */
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 6, 0)
#define HAVE_ON_EACH_MATCH_SYMBOL 1
#else
#define HAVE_ON_EACH_MATCH_SYMBOL 0
#endif

static unsigned long (*kallsyms_lookup_name_fn)(const char *name) = NULL;
static const char *(*kallsyms_lookup_fn)(unsigned long addr, unsigned long *symbolsize, unsigned long *offset,
                                         char **modname, char *namebuf) = NULL;

/* The walker lost the callback's `struct module *` in v6.4, so both the POINTER's type and the
 * callbacks below are gated at 6.4 - the argument carried module ownership. */
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 4, 0)
typedef int (*ksu_on_each_symbol_fn_t)(int (*fn)(void *, const char *, unsigned long), void *data);
#else
typedef int (*ksu_on_each_symbol_fn_t)(int (*fn)(void *, const char *, struct module *, unsigned long), void *data);
#endif

static ksu_on_each_symbol_fn_t kallsyms_on_each_symbol_fn = NULL;

#if HAVE_ON_EACH_MATCH_SYMBOL
static int (*kallsyms_on_each_match_symbol_fn)(int (*fn)(void *, unsigned long), const char *name, void *data) = NULL;
static int find_kernel_symbol_exact_cb(void *data, unsigned long addr)
{
    *(unsigned long *)data = addr;
    return 0;
}
#endif

static __nocfi void *ksu_bootstrap_symbol(const char *name)
{
    struct kprobe kp;
    void *addr = NULL;

    memset(&kp, 0, sizeof(kp));
    kp.symbol_name = (void *)name;

    if (!register_kprobe(&kp)) {
        addr = (void *)kp.addr;
        unregister_kprobe(&kp);
    }

    if (!addr)
        pr_warn("symbol_resolver: cannot bootstrap %s (kprobe could not resolve it)\n", name);

    return addr;
}

struct ksu_lookup_symbol_ctx {
    const char *symbol_name;
    size_t symbol_len;
    void *match;
};

struct ksu_exact_name_ctx {
    const char *symbol_name;
    unsigned long addr;
};

#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 4, 0)
static int ksu_exact_name_cb(void *data, const char *name, unsigned long addr)
#else
static int ksu_exact_name_cb(void *data, const char *name, struct module *mod, unsigned long addr)
#endif
{
    struct ksu_exact_name_ctx *ctx = data;

#if LINUX_VERSION_CODE < KERNEL_VERSION(6, 4, 0)
    /* OWNERSHIP before 6.4: a non-NULL `mod` means another module provides the symbol. */
    if (mod)
        return 0;
#endif

    if (!name || strcmp(name, ctx->symbol_name) != 0)
        return 0;

    ctx->addr = addr;
    return 1;	/* stop the walk */
}

/* Same shape, but it keeps every match (see ksu_find_symbol_all()). */
struct ksu_all_names_ctx {
    const char *symbol_name;
    unsigned long *addrs;
    int max;
    int n;
};

#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 4, 0)
static int ksu_all_names_cb(void *data, const char *name, unsigned long addr)
#else
static int ksu_all_names_cb(void *data, const char *name, struct module *mod, unsigned long addr)
#endif
{
    struct ksu_all_names_ctx *ctx = data;
    int i;

#if LINUX_VERSION_CODE < KERNEL_VERSION(6, 4, 0)
    if (mod)
        return 0;
#endif

    if (!name || !addr || strcmp(name, ctx->symbol_name) != 0)
        return 0;

    for (i = 0; i < ctx->n; i++)
        if (ctx->addrs[i] == addr)
            return 0;			/* the walk can report a symbol twice (aliases) */

    if (ctx->n < ctx->max)
        ctx->addrs[ctx->n++] = addr;
    return 0;				/* keep walking: uniqueness is not assumed */
}

unsigned long __nocfi find_kernel_symbol_exact(const char *symbol_name)
{
    unsigned long addr = 0;

    if (!symbol_name || !symbol_name[0])
        return 0;

#if HAVE_ON_EACH_MATCH_SYMBOL
    /* 6.1+ can match the exact name, but carries no ownership check - tried first only. */
    if (likely(kallsyms_on_each_match_symbol_fn)) {
        kallsyms_on_each_match_symbol_fn(find_kernel_symbol_exact_cb, symbol_name, &addr);
        return addr;
    }
#endif

    if (unlikely(!kallsyms_lookup_name_fn))
        return 0;

    addr = kallsyms_lookup_name_fn(symbol_name);
    if (!addr)
        return 0;	/* walking kallsyms for address 0 answers nothing */

    if (likely(kallsyms_lookup_fn)) {

        char *module_name = NULL;
        char buf[KSYM_SYMBOL_LEN];

        kallsyms_lookup_fn(addr, NULL, NULL, &module_name, buf);
        if (unlikely(module_name)) {
            pr_warn("ignore symbol %s of module %s\n", symbol_name, module_name);
            return 0;
        }
        return addr;
    }

    if (kallsyms_on_each_symbol_fn) {
        struct ksu_exact_name_ctx ctx = { .symbol_name = symbol_name };

        kallsyms_on_each_symbol_fn(ksu_exact_name_cb, &ctx);
        if (ctx.addr != addr) {
            pr_warn("ignore symbol %s: the kallsyms walk did not confirm it as vmlinux's\n", symbol_name);
            return 0;
        }
        return addr;
    }

    pr_warn("ignore symbol %s: its owner cannot be checked on this kernel\n", symbol_name);
    return 0;
}

/* Raw name lookup through the bootstrapped kallsyms_lookup_name(), for names the KERNEL does not
 * own: its implementation ends in module_kallsyms_lookup_name(), so a symbol provided by
 * kernelsu.ko is found too - which is why find_kernel_symbol_exact() (module owners refused) is not
 * the tool for callers that need exactly that.  0 = unknown name, or the resolver is not up; never
 * sleeps.  __nocfi because the call goes through the resolver's function pointer. */
unsigned long __nocfi ksu_kallsyms_lookup_name(const char *name)
{
    if (!name || !name[0] || unlikely(!kallsyms_lookup_name_fn))
        return 0;

    return kallsyms_lookup_name_fn(name);
}

int __nocfi ksu_find_symbol_all(const char *name, unsigned long *addrs, int max)
{
    int n = 0;

    if (!name || !name[0] || !addrs || max <= 0)
        return 0;

    if (kallsyms_on_each_symbol_fn) {
        struct ksu_all_names_ctx ctx = { .symbol_name = name, .addrs = addrs, .max = max, .n = 0 };

        kallsyms_on_each_symbol_fn(ksu_all_names_cb, &ctx);
        n = ctx.n;
    }

    if (n == 0) {

        unsigned long one = find_kernel_symbol_exact(name);

        if (one) {
            addrs[0] = one;
            n = 1;
        }
    }

    return n;
}

static inline bool ksu_symbol_has_suffix(const char *name, size_t name_len, const char *suffix, size_t suffix_len)
{
    return name_len >= suffix_len && strcmp(name + name_len - suffix_len, suffix) == 0;
}

#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 4, 0)
static int lookup_symbol_variant_cb(void *data, const char *name, unsigned long addr)
#else
static int lookup_symbol_variant_cb(void *data, const char *name, struct module *mod, unsigned long addr)
#endif
{
    struct ksu_lookup_symbol_ctx *ctx = data;
    size_t name_len;

    if (!name || !addr)
        return 0;

    name_len = strlen(name);

    if (strcmp(name, ctx->symbol_name) != 0) {
        if (name_len <= ctx->symbol_len || strncmp(name, ctx->symbol_name, ctx->symbol_len) != 0 ||
            name[ctx->symbol_len] != '.')
            return 0;
    }

#if !USE_KCFI
    if (ksu_symbol_has_suffix(name, name_len, cfi_suffix, cfi_suffix_len)) {
        ctx->match = (void *)addr;
        SUSFS_LOGI("use .cfi_jt variant: %s\n", name);
        return 1;
    }
#endif

    if (!ctx->match) {
        ctx->match = (void *)addr;
        SUSFS_LOGI("found variant: %s\n", name);
#if USE_KCFI
        return 1;
#endif
    }

    return 0;
}

static __nocfi void *resolve_symbol_variant(const char *symbol_name, size_t symbol_len)
{
    struct ksu_lookup_symbol_ctx ctx = {
        .symbol_name = symbol_name,
        .symbol_len = symbol_len,
    };

    if (unlikely(!kallsyms_on_each_symbol_fn))
        return NULL;

    kallsyms_on_each_symbol_fn(lookup_symbol_variant_cb, &ctx);

    return ctx.match;
}

void *ksu_resolve_symbol_for_functable_hook(const char *symbol_name)
{
    void *addr;
    size_t symbol_len;

    if (!symbol_name || !symbol_name[0])
        return NULL;

    symbol_len = strlen(symbol_name);

#if !USE_KCFI
    char cfi_name[KSYM_NAME_LEN];
    snprintf(cfi_name, sizeof(cfi_name), "%s.cfi_jt", symbol_name);
    addr = (void *)find_kernel_symbol_exact(cfi_name);
    if (addr)
        return addr;

    addr = resolve_symbol_variant(symbol_name, symbol_len);
    if (addr)
        return addr;

    return (void *)find_kernel_symbol_exact(symbol_name);
#else
    addr = (void *)find_kernel_symbol_exact(symbol_name);
    if (addr)
        return addr;

    return resolve_symbol_variant(symbol_name, symbol_len);
#endif
}

/* __nocfi like every other function here that reaches a resolved symbol: the call to
 * kallsyms_lookup() goes through a function pointer, so an instrumented call site would be
 * checked against the kernel's type id - and that check panics when it does not match.
 * 6.12/6.18 reach this through the static-call takeover (lsm_hook.c), i.e. it is on a real
 * path, not a debug one; tools/cfi_sites.py now fails the build if it is ever un-annotated
 * again. */
int __nocfi ksu_symbol_name_of(unsigned long addr, char *buf, char **module_out)
{
    char *modname = NULL;

    if (module_out)
        *module_out = NULL;
    if (!buf)
        return -EINVAL;
    buf[0] = '\0';
    if (!kallsyms_lookup_fn)
        return -ENOSYS;
    if (!addr)
        return -EINVAL;
    if (!kallsyms_lookup_fn(addr, NULL, NULL, &modname, buf))
        return -ENOENT;
    if (module_out)
        *module_out = modname;

    return (int)strlen(buf);
}

void __init ksu_init_symbol_resolver(void)
{
    int match_ok = 0;

    /* Bootstrap by NAME through a kprobe, never linked against; NULL is a degradation. */
    kallsyms_lookup_name_fn = ksu_bootstrap_symbol("kallsyms_lookup_name");
    kallsyms_lookup_fn = ksu_bootstrap_symbol("kallsyms_lookup");
    kallsyms_on_each_symbol_fn = ksu_bootstrap_symbol("kallsyms_on_each_symbol");
#if ALWAYS_HAVE_ON_EACH_SYMBOL
    /* From 5.19 the walker always exists, so its absence is a real loss of coverage. */
    if (!kallsyms_on_each_symbol_fn)
        pr_warn("kallsyms_on_each_symbol exists in every 5.19+ kernel but did not resolve!\n");
#endif
#if HAVE_ON_EACH_MATCH_SYMBOL
    kallsyms_on_each_match_symbol_fn = ksu_bootstrap_symbol("kallsyms_on_each_match_symbol");
    match_ok = !!kallsyms_on_each_match_symbol_fn;
#endif

    /* Whether these came up decides which mechanism resolves symbols. */
    SUSFS_LOGI("symbol_resolver: kprobe bootstrap (1 = usable): lookup_name=%d lookup=%d walker=%d match=%d\n",
               !!kallsyms_lookup_name_fn, !!kallsyms_lookup_fn, !!kallsyms_on_each_symbol_fn, match_ok);
}
