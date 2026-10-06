/* SPDX-License-Identifier: GPL-2.0 */

#include <linux/compiler.h>
#include <linux/errno.h>
#include <linux/kernel.h>
#include <linux/lsm_hooks.h>
#include <linux/mutex.h>
#include <linux/delay.h>
#include <linux/rcupdate.h>
#include <linux/string.h>
#include <linux/version.h>		/* LINUX_VERSION_CODE for the gates below (do not rely on a transitive include) */

#include "symbol_resolver.h"
#include "lsm_hook.h"
#include "patch_memory.h"
#include "susfs_log.h"
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 12, 0)
#include <linux/static_call.h>		/* __static_call_update() - EXPORT_SYMBOL_GPL */
#include <linux/static_call_types.h>	/* struct static_call_key */
#include <linux/lsm_count.h>		/* MAX_LSM_COUNT = the slots each hook has */
#include <linux/kallsyms.h>		/* KSYM_SYMBOL_LEN, to name the target function */
#include <linux/uaccess.h>		/* copy_from_kernel_nofault(), layout probe */
#endif

struct ksu_lsm_hook_entry {
    struct ksu_lsm_hook *hook;
};

/* Defined below; called from ksu_unregister_lsm_hook(). */
static void ksu_lsm_hook_drain(void);

static DEFINE_MUTEX(ksu_lsm_hook_lock);
static struct ksu_lsm_hook_entry ksu_lsm_hook_entries[16];
static int ksu_lsm_hook_count;

static bool ksu_lsm_hook_is_tracked(struct ksu_lsm_hook *hook)
{
    int i;

    for (i = 0; i < ksu_lsm_hook_count; i++) {
        if (ksu_lsm_hook_entries[i].hook == hook)
            return true;
    }

    return false;
}

static int ksu_lsm_hook_track(struct ksu_lsm_hook *hook)
{
    if (ksu_lsm_hook_is_tracked(hook))
        return 0;

    if (ksu_lsm_hook_count >= ARRAY_SIZE(ksu_lsm_hook_entries)) {
        pr_err("lsm_hook: tracking table full, cannot record %s\n", hook->head_name ?: "unknown");
        return -ENOSPC;
    }

    ksu_lsm_hook_entries[ksu_lsm_hook_count++].hook = hook;
    return 0;
}

static void ksu_lsm_hook_untrack(struct ksu_lsm_hook *hook)
{
    int i;

    for (i = 0; i < ksu_lsm_hook_count; i++) {
        if (ksu_lsm_hook_entries[i].hook != hook)
            continue;

        ksu_lsm_hook_entries[i] = ksu_lsm_hook_entries[--ksu_lsm_hook_count];
        return;
    }
}

static int ksu_lsm_hook_patch_slot(void **slot, void *value)
{
    void *patched = value;
    int ret;

    ret = ksu_patch_text(slot, &patched, sizeof(patched), KSU_PATCH_TEXT_FLUSH_DCACHE);
    if (!ret)
        smp_wmb();

    return ret;
}

#if LINUX_VERSION_CODE < KERNEL_VERSION(6, 12, 0)

static int ksu_lsm_hook_head_at(unsigned long heads_addr, struct ksu_lsm_hook *hook,
                                struct hlist_head **out)
{
    struct hlist_head *head;
    struct security_hook_list *first;

    if (hook->head_offset + sizeof(struct hlist_head) > sizeof(struct security_hook_heads)) {
        pr_err("lsm_hook: %s: head offset %#lx is outside security_hook_heads\n",
                hook->head_name ?: "unknown", (unsigned long)hook->head_offset);
        return -EINVAL;
    }

    head = (struct hlist_head *)(heads_addr + hook->head_offset);
    first = hlist_entry_safe(READ_ONCE(head->first), struct security_hook_list, list);

    if (!first) {
        pr_err("lsm_hook: %s: hook list is empty - refusing to insert (nothing to cross-check the head offset against)\n",
                hook->head_name ?: "unknown");
        return -ENOENT;
    }
    if (first->head != head) {
        pr_err("lsm_hook: %s: entry at %px reports head %px, computed %px - struct security_hook_heads layout mismatch, refusing to patch\n",
                hook->head_name ?: "unknown", first, first->head, head);
        return -EINVAL;
    }

    *out = head;
    return 0;
}

/* Insert our node at the head of the list; lock held, head already validated. */
static int ksu_lsm_hook_insert_head(struct ksu_lsm_hook *hook, struct hlist_head *head)
{
    struct security_hook_list *node = &hook->list;
    struct hlist_node *first = READ_ONCE(head->first);
    struct security_hook_list *first_entry;
    int ret;

    first_entry = hlist_entry_safe(first, struct security_hook_list, list);
    if (!first_entry || first_entry->head != head) {
        pr_err("lsm_hook: %s: head %px changed under us, refusing to insert\n",
                hook->head_name ?: "unknown", head);
        return -EAGAIN;
    }

    memset(node, 0, sizeof(*node));
    *(void **)((char *)node + hook->hook_offset) = hook->replacement;
    node->head = head;
    node->lsm = "susfs";
    node->list.next = first;
    node->list.pprev = &head->first;

    /* 1. head->first, in __lsm_ro_after_init memory: this write publishes the node. */
    ret = ksu_lsm_hook_patch_slot((void **)&head->first, node);
    if (ret)
        return ret;

    ret = ksu_lsm_hook_patch_slot((void **)&first->pprev, &node->list.next);
    if (ret) {
        /* Roll back the publication - a wrong-way neighbour corrupts the list. */
        if (ksu_lsm_hook_patch_slot((void **)&head->first, first))
            pr_err("lsm_hook: %s: failed to roll back head->first after a failed insert\n",
                    hook->head_name ?: "unknown");
        node->list.next = NULL;
        node->list.pprev = NULL;
        return ret;
    }

    hook->entry = node;
    SUSFS_LOGI("lsm_hook: inserted %s as the first node of its list (head %px, before %px, replacement %px)\n",
            hook->head_name ?: "unknown", head, first, hook->replacement);
    return 0;
}

/* Unlink our node; the words it writes live in memory only ksu_patch_text() may touch. */
static int ksu_lsm_hook_remove_head(struct ksu_lsm_hook *hook)
{
    struct hlist_node **pprev = hook->list.list.pprev;
    struct hlist_node *next = READ_ONCE(hook->list.list.next);
    int ret;

    if (!pprev || READ_ONCE(*pprev) != &hook->list.list) {
        pr_err("lsm_hook: %s: back pointer %px does not point at our node - refusing to unlink\n",
                hook->head_name ?: "unknown", pprev);
        return -EINVAL;
    }

    ret = ksu_lsm_hook_patch_slot((void **)pprev, next);
    if (ret)
        return ret;

    if (next) {
        ret = ksu_lsm_hook_patch_slot((void **)&next->pprev, pprev);
        if (ret) {
            /* Our node is already out; re-link rather than leave a stale back pointer. */
            if (ksu_lsm_hook_patch_slot((void **)pprev, &hook->list.list))
                pr_err("lsm_hook: %s: failed to re-link our node after a failed unlink\n",
                        hook->head_name ?: "unknown");
            return ret;
        }
    }

    hook->list.list.next = NULL;
    hook->list.list.pprev = NULL;
    hook->entry = NULL;
    SUSFS_LOGI("lsm_hook: removed %s node from its list\n", hook->head_name ?: "unknown");
    return 0;
}
#endif /* < 6.12 */

#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 12, 0)

static void (*ksu_static_call_update_fn)(struct static_call_key *key, void *tramp, void *func);

static __nocfi void ksu_lsm_call_scall_update(struct static_call_key *key, void *tramp, void *func)
{
    ksu_static_call_update_fn(key, tramp, func);
}

static int ksu_lsm_hook_update_scall(struct lsm_static_call *scall, void *value)
{
    if (ksu_static_call_update_fn) {
        ksu_lsm_call_scall_update(scall->key, scall->trampoline, value);
        smp_wmb();
        return 0;
    }

    __static_call_update(scall->key, scall->trampoline, value);
    smp_wmb();
    return 0;
}

#define KSU_LSM_SLOTS_PER_HOOK	MAX_LSM_COUNT

#define KSU_LSM_KPTR_MIN	0xff00000000000000UL

static unsigned long ksu_lsm_scalls_addr;

static bool ksu_lsm_kptr_plausible(const void *p)
{
    return (unsigned long)p >= KSU_LSM_KPTR_MIN;
}

static int ksu_lsm_read_ptr(const void *addr, void *out)
{
    memset(out, 0, sizeof(void *));
    return (int)copy_from_kernel_nofault(out, addr, sizeof(void *));
}

/* Same implementation as @want?  Allows the ".clone"/".constprop.0" suffix a compiler adds. */
static bool ksu_lsm_name_is(const char *name, const char *want)
{
    size_t n = strlen(want);

    if (strncmp(name, want, n) != 0)
        return false;

    return name[n] == '\0' || name[n] == '.';
}

/* Is @fn one of the addresses kallsyms has for @name?
 *
 * The identity test cannot lean on the name kallsyms reports for an ADDRESS.  A lookup by
 * address names one symbol per address, so when two functions end up at the same address
 * (identical code folded together, or a vendor alias) that name is whichever symbol comes
 * first - and it can be the other one.  Measured on a 6.12.23 vendor kernel: the address
 * SELinux registered for inode_getattr resolves to `selinux_current_getsecid_subj`, which
 * is a symbol at that very address; the slot was right, the reported name was not, and the
 * module refused to load over it.
 *
 * So the question is asked the other way round: does kallsyms have ANY address called
 * @name that equals this pointer?  @n_addrs receives how many addresses the name has at
 * all, so a caller can log "this kernel has no such name" rather than "it is another name".
 * The enumeration is the same one the multi-match fdinfo probe uses. */
static bool ksu_lsm_addr_is_named(void *fn, const char *name, int *n_addrs)
{
    unsigned long addrs[8];
    int n, i;

    n = ksu_find_symbol_all(name, addrs, (int)ARRAY_SIZE(addrs));
    if (n_addrs)
        *n_addrs = n;

    for (i = 0; i < n; i++) {
        if (addrs[i] == (unsigned long)fn)
            return true;
    }

    return false;
}

static int ksu_lsm_fn_is_selinux_hook(void *fn, const char *member, void *expect)
{
    char buf[KSYM_SYMBOL_LEN];
    char want[64];
    char *mod = NULL;
    int len, n_addrs = 0;

    snprintf(want, sizeof(want), "selinux_%s", member);

    len = ksu_symbol_name_of((unsigned long)fn, buf, &mod);

    /* The name of the address, when it is SELinux's own symbol (a module-owned one is
     * somebody else's function and is refused below whatever it is called). */
    if (len > 0 && !mod) {
        if (ksu_lsm_name_is(buf, want))
            return 0;
        if (strstr(buf, member)) {
            pr_warn("lsm_hook: %s: %px is not %s but its name contains it (%s) - accepting\n",
                    member, fn, want, buf);
            return 0;
        }
    }

    /* The address itself, when it is one kallsyms has for the name we want.  This is what
     * covers the folded/aliased case above, and it is still a real identity check: the name
     * has to resolve to this exact pointer. */
    if (!mod && ksu_lsm_addr_is_named(fn, want, &n_addrs)) {
        pr_warn("lsm_hook: %s: %px is %s by address - kallsyms names that address %s; accepting\n",
                member, fn, want, buf[0] ? buf : "(nothing)");
        return 0;
    }

    if (mod) {
        pr_warn("lsm_hook: %s: %px resolves to %s [%s], which is neither %s nor contains \"%s\"\n",
                member, fn, buf, mod, want, member);
        return -EINVAL;
    }

    if (len > 0) {
        pr_warn("lsm_hook: %s: %px resolves to %s, which is neither %s nor contains \"%s\" (%d address(es) are named %s, none of them this one)\n",
                member, fn, buf, want, member, n_addrs, want);
        return -EINVAL;
    }

    if (n_addrs == 0)
        pr_warn("lsm_hook: %s: %px cannot be named, and this kernel has no address named %s at all\n",
                member, fn, want);

    /* Nothing named that address, so the identity of the name could not be checked above -
     * this is the path this function has always had: compare against the address resolved
     * for `selinux_<member>`, and with nothing to compare against, refuse. */
    if (expect)
        return (fn == expect) ? 0 : -EINVAL;

    return -ENOSYS;
}

/* ---- locating this hook's slot in static_calls_table, on a kernel we did not build against
 *
 * offsetof(struct lsm_static_calls_table, <member>) is only the right slot when the kernel's
 * hook order AND its MAX_LSM_COUNT match the tree this module was compiled against.  Measured
 * on 6.12.23-android16-4k they do not: MAX_LSM_COUNT is 3 there (its per-hook static call keys
 * are named ..._0/_1/_2) and 5 in the DDK tree, so every offset is 5/3 too large and lands on a
 * LATER hook's array.  That array's SELinux entry passes every structural check - its `scalls`
 * points back at the array being read, its lsmid is SELinux's, and `key->func` equals the
 * entry's hook word, which is the SAME word for all 13 hooks because `hook` is a union and
 * every member sits at offset 0.  Only the function the kernel registered can tell them apart.
 *
 * So the slot is found by identity: resolve the addresses kallsyms has for `selinux_<member>`
 * once, then scan the table for the element whose SELinux entry holds one of them.  Bounded by
 * the table's own neighbour in .data (lsm_active_cnt) and, failing that, by a hard cap; nothing
 * matched means refuse, exactly as before. */
#define KSU_LSM_SCAN_MAX	(64 * 1024)

static unsigned long ksu_lsm_scan_end;	/* 0 = not resolved yet, ~0UL = no neighbour available */

static unsigned long ksu_lsm_scalls_end(void)
{
    unsigned long next;

    if (!ksu_lsm_scan_end) {
        next = find_kernel_symbol_exact("lsm_active_cnt");
        ksu_lsm_scan_end = (next > ksu_lsm_scalls_addr &&
                            next - ksu_lsm_scalls_addr < KSU_LSM_SCAN_MAX) ? next : ~0UL;
    }

    return ksu_lsm_scan_end == ~0UL ? ksu_lsm_scalls_addr + KSU_LSM_SCAN_MAX : ksu_lsm_scan_end;
}

/* Is @s an occupied static-call slot whose SELinux entry is worth looking at?
 *
 * Scan-friendly on purpose: anything that does not look like a slot is skipped rather than
 * reported, because the scan walks elements the previous code never touched.  Returns 0 with
 * *hl_out == NULL for "not this one", and fills *hl_out / *cur_out when it is a SELinux slot.
 * Nothing here identifies the HOOK - that is the caller's address test. */
static void ksu_lsm_slot_selinux(struct lsm_static_call *s, struct ksu_lsm_hook *hook,
                                 struct security_hook_list **hl_out, void **cur_out)
{
    unsigned long end = ksu_lsm_scalls_end();
    struct security_hook_list *hl;
    void *key, *tramp, *scalls, *lsmid, *namep, *hookfn, *cur;
    char namebuf[16];

    *hl_out = NULL;
    *cur_out = NULL;

    if (ksu_lsm_read_ptr(&s->key, &key) || ksu_lsm_read_ptr(&s->trampoline, &tramp) ||
        ksu_lsm_read_ptr(&s->hl, &hl))
        return;
    if (!key || !hl)
        return;			/* empty: no LSM implements this hook in this slot */
    if (!ksu_lsm_kptr_plausible(key) || !ksu_lsm_kptr_plausible(hl) ||
        (tramp && !ksu_lsm_kptr_plausible(tramp)))
        return;

    if (ksu_lsm_read_ptr((const char *)hl + offsetof(struct security_hook_list, scalls), &scalls))
        return;
    if ((unsigned long)scalls < ksu_lsm_scalls_addr || (unsigned long)scalls >= end ||
        ((unsigned long)scalls & (sizeof(void *) - 1)))
        return;			/* not an array inside the table: not a slot we can reason about */

    if (ksu_lsm_read_ptr((const char *)hl + offsetof(struct security_hook_list, lsmid), &lsmid) ||
        !ksu_lsm_kptr_plausible(lsmid) ||
        ksu_lsm_read_ptr((const char *)lsmid + offsetof(struct lsm_id, name), &namep) ||
        !ksu_lsm_kptr_plausible(namep) ||
        copy_from_kernel_nofault(namebuf, namep, 8))
        return;
    namebuf[8] = '\0';
    if (strncmp(namebuf, "selinux", 8) != 0)
        return;			/* capability, safesetid, landlock, bpf-lsm, ... */

    if (ksu_lsm_read_ptr((const char *)key + offsetof(struct static_call_key, func), &cur) ||
        ksu_lsm_read_ptr((const char *)hl + hook->hook_offset, &hookfn) ||
        !cur || !hookfn || cur != hookfn)
        return;			/* mid-update, or not the shape of a static call */

    *hl_out = hl;
    *cur_out = cur;
}

/* Scan the table for the slot whose SELinux entry registered one of @addrs. */
static void ksu_lsm_scan_slot(struct ksu_lsm_hook *hook, const unsigned long *addrs, int n_addrs,
                              struct lsm_static_call **chosen_out,
                              struct security_hook_list **hl_out, void **orig_out,
                              unsigned long *scanned_out)
{
    unsigned long end = ksu_lsm_scalls_end();
    unsigned long p;
    int i;

    *chosen_out = NULL;
    *hl_out = NULL;
    *orig_out = NULL;
    *scanned_out = 0;

    for (p = ksu_lsm_scalls_addr; p + sizeof(struct lsm_static_call) <= end;
         p += sizeof(struct lsm_static_call)) {
        struct security_hook_list *hl;
        void *cur;

        (*scanned_out)++;
        ksu_lsm_slot_selinux((struct lsm_static_call *)p, hook, &hl, &cur);
        if (!hl)
            continue;

        for (i = 0; i < n_addrs; i++) {
            if (cur != (void *)addrs[i])
                continue;
            *chosen_out = (struct lsm_static_call *)p;
            *hl_out = hl;
            *orig_out = cur;
            return;
        }
    }
}

/* Lock held; success sets ->scall/->entry/->original and the static call to the replacement. */
static int ksu_lsm_hook_insert_scall(struct ksu_lsm_hook *hook)
{
    struct lsm_static_call *slots;
    struct lsm_static_call *chosen = NULL;
    struct security_hook_list *chosen_hl = NULL;
    void *chosen_orig = NULL;
    unsigned long addrs[8];
    unsigned long scanned = 0;
    void *expect = NULL;
    char want[64];
    int i, n_addrs, ret;

    if (!hook->head_name) {
        pr_err("lsm_hook: insert: hook has no head_name, cannot identify its static calls\n");
        return -EINVAL;
    }

    if (!ksu_lsm_scalls_addr) {
        ksu_lsm_scalls_addr = find_kernel_symbol_exact("static_calls_table");
        if (!ksu_lsm_scalls_addr) {
            pr_err("lsm_hook: insert: static_calls_table not resolved\n");
            return -ENOENT;
        }
        SUSFS_LOGI("lsm_hook: static_calls_table at %px (%d slots per hook)\n",
                (void *)ksu_lsm_scalls_addr, (int)KSU_LSM_SLOTS_PER_HOOK);
    }

    snprintf(want, sizeof(want), "selinux_%s", hook->head_name);
    expect = ksu_resolve_symbol_for_functable_hook(want);

    /* What the kernel registered is what identifies the slot, so resolve the addresses kallsyms
     * has for `selinux_<member>` (normally one) and scan the table for it. */
    n_addrs = ksu_find_symbol_all(want, addrs, (int)ARRAY_SIZE(addrs));
    if (n_addrs == 0 && expect) {
        addrs[0] = (unsigned long)expect;
        n_addrs = 1;
    }

    if (n_addrs) {
        ksu_lsm_scan_slot(hook, addrs, n_addrs, &chosen, &chosen_hl, &chosen_orig, &scanned);
        if (chosen) {
            unsigned long idx = (unsigned long)(chosen -
                                  (struct lsm_static_call *)ksu_lsm_scalls_addr);
            unsigned long off = hook->head_offset / sizeof(struct lsm_static_call);

            if (idx != off) {
                pr_warn("lsm_hook: %s: its slot is element %lu of static_calls_table while offsetof() names %lu - this kernel's MAX_LSM_COUNT or hook order differs from the tree this module was built against (%d slots per hook assumed)\n",
                        hook->head_name, idx, off, (int)KSU_LSM_SLOTS_PER_HOOK);
            }
            SUSFS_LOGI("lsm_hook: %s: slot found by identity at element %lu (%d address(es) named %s, %lu elements scanned)\n",
                    hook->head_name, idx, n_addrs, want, scanned);
        }
    }

    /* Fallback, only when nothing was found by identity: the slot the build-time offset names,
     * judged by the NAME of the function in it.  That is what this module always did, and it
     * keeps the case a name-based test can accept working (a vendor wrapper whose name merely
     * contains the member).  It fails closed: an offset that lands on another hook is refused
     * by the identity test inside the loop. */
    slots = (struct lsm_static_call *)(ksu_lsm_scalls_addr + hook->head_offset);

    for (i = 0; !chosen && i < KSU_LSM_SLOTS_PER_HOOK; i++) {
        struct lsm_static_call *s = &slots[i];
        struct security_hook_list *hl;
        void *key, *tramp, *scalls, *lsmid, *namep, *hookfn, *cur;
        char namebuf[16];

        if (ksu_lsm_read_ptr(&s->key, &key) ||
            ksu_lsm_read_ptr(&s->trampoline, &tramp) ||
            ksu_lsm_read_ptr(&s->hl, &hl)) {
            pr_err("lsm_hook: insert: %s: slot %d of static_calls_table is not readable - refusing\n",
                    hook->head_name, i);
            return -EFAULT;
        }
        if (!hl)
            continue;	/* empty slot: no LSM implements this hook there */

        if (!key || !ksu_lsm_kptr_plausible(key) || !ksu_lsm_kptr_plausible(hl) ||
            (tramp && !ksu_lsm_kptr_plausible(tramp))) {
            pr_err("lsm_hook: insert: %s: slot %d has implausible key/trampoline/hl (%px/%px/%px) - struct lsm_static_call layout mismatch, refusing\n",
                    hook->head_name, i, key, tramp, hl);
            return -EINVAL;
        }

        if (ksu_lsm_read_ptr((const char *)hl + offsetof(struct security_hook_list, scalls), &scalls) ||
            scalls != (void *)slots) {
            pr_err("lsm_hook: insert: %s: slot %d entry %px reports scalls %px, expected %px - struct/table layout mismatch, refusing\n",
                    hook->head_name, i, hl, scalls, slots);
            return -EINVAL;
        }

        if (ksu_lsm_read_ptr((const char *)hl + offsetof(struct security_hook_list, lsmid), &lsmid) ||
            !ksu_lsm_kptr_plausible(lsmid) ||
            ksu_lsm_read_ptr((const char *)lsmid + offsetof(struct lsm_id, name), &namep) ||
            !ksu_lsm_kptr_plausible(namep) ||
            copy_from_kernel_nofault(namebuf, namep, 8)) {
            pr_err("lsm_hook: insert: %s: slot %d entry %px has no readable lsm_id name - refusing\n",
                    hook->head_name, i, hl);
            return -EINVAL;
        }
        namebuf[8] = '\0';
        if (strncmp(namebuf, "selinux", 8) != 0)
            continue;	/* capabilities, safesetid, landlock, bpf-lsm, ... */

        if (ksu_lsm_read_ptr((const char *)key + offsetof(struct static_call_key, func), &cur) ||
            ksu_lsm_read_ptr((const char *)hl + hook->hook_offset, &hookfn) ||
            !cur || !hookfn) {
            pr_err("lsm_hook: insert: %s: slot %d (selinux) has no readable current target - refusing\n",
                    hook->head_name, i);
            return -EINVAL;
        }
        if (cur != hookfn) {
            pr_err("lsm_hook: insert: %s: slot %d (selinux) calls %px while the entry's hook word holds %px - layout mismatch, refusing\n",
                    hook->head_name, i, cur, hookfn);
            return -EINVAL;
        }

        ret = ksu_lsm_fn_is_selinux_hook(cur, hook->head_name, expect);
        if (ret) {
            pr_err("lsm_hook: insert: %s: slot %d (selinux) holds %px, which is not %s (%d) - another owner or a shifted layout, refusing\n",
                    hook->head_name, i, cur, want, ret);
            return ret == -ENOSYS ? -ENOSYS : -EINVAL;
        }

        chosen = s;
        chosen_hl = hl;
        chosen_orig = cur;
        break;
    }

    if (!chosen) {
        pr_err("lsm_hook: insert: %s: no slot for it among the %lu scanned elements of static_calls_table, and the element offsetof() names (%lu) is not it either (%d address(es) named %s) - refusing\n",
                hook->head_name, scanned,
                (unsigned long)(hook->head_offset / sizeof(struct lsm_static_call)),
                n_addrs, want);
        return -ENOENT;
    }

    for (i = 0; i < ksu_lsm_hook_count; i++) {
        if (ksu_lsm_hook_entries[i].hook->scall == chosen) {
            pr_err("lsm_hook: insert: %s: that static-call slot is already taken over by %s\n",
                    hook->head_name, ksu_lsm_hook_entries[i].hook->head_name ?: "another hook");
            return -EALREADY;
        }
    }

    ret = ksu_lsm_hook_track(hook);
    if (ret) {
        pr_err("lsm_hook: too many hooks to track: %d\n", ret);
        return ret;
    }

    hook->scall = chosen;
    hook->entry = chosen_hl;
    hook->original = chosen_orig;
    smp_wmb();
    ksu_lsm_hook_update_scall(chosen, hook->replacement);

    SUSFS_LOGI("lsm_hook: insert via static call slot (selinux, element %lu, %s static call) %s: %px -> %px\n",
            (unsigned long)(chosen - (struct lsm_static_call *)ksu_lsm_scalls_addr),
            chosen->trampoline ? "trampolined" : "key->func",
            hook->head_name, chosen_orig, hook->replacement);
    return 0;
}
#endif

int ksu_lsm_hook(struct ksu_lsm_hook *hook)
{
    int ret = 0;
    struct security_hook_list *entry;
    void *target;
    const char *target_name;
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 12, 0)
    static unsigned long scalls_addr = 0;
    struct lsm_static_call *scalls = NULL;
    static size_t scalls_count = 0;
    struct security_hook_list *selected_entry = NULL;
    struct lsm_static_call *selected_scall = NULL;
    void **selected_slot = NULL;
    void *selected_origin = NULL;
    size_t i;
#else
    unsigned long heads_addr;
    struct hlist_head *head;
    struct security_hook_list *selected_entry = NULL;
    void **selected_slot = NULL;
    void *selected_origin = NULL;
#endif

    if (!hook || !hook->replacement)
        return -EINVAL;

    mutex_lock(&ksu_lsm_hook_lock);

    if (hook->entry) {
        ret = -EALREADY;
        goto out_unlock;
    }

    if (hook->insert) {

#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 12, 0)
        ret = ksu_lsm_hook_insert_scall(hook);
        goto out_unlock;
#else
        heads_addr = find_kernel_symbol_exact("security_hook_heads");
        if (!heads_addr) {
            pr_err("lsm_hook: failed to resolve security_hook_heads\n");
            ret = -ENOENT;
            goto out_unlock;
        }

        ret = ksu_lsm_hook_head_at(heads_addr, hook, &head);
        if (ret)
            goto out_unlock;

        ret = ksu_lsm_hook_track(hook);
        if (ret) {
            pr_err("lsm_hook: too many hooks to track: %d\n", ret);
            goto out_unlock;
        }

        ret = ksu_lsm_hook_insert_head(hook, head);
        if (ret) {
            pr_err("lsm_hook: failed to insert %s at the head of its list: %d\n",
                    hook->head_name ?: "unknown", ret);
            ksu_lsm_hook_untrack(hook);
            goto out_unlock;
        }
        goto out_unlock;
#endif
    }

    /* ---- replace path: find the entry whose function slot holds the resolved symbol. ---- */
    target_name = hook->target_name;
    if (!target_name) {
        pr_err("lsm_hook: hook %s: target_name is required\n", hook->head_name ?: "unknown");
        ret = -EINVAL;
        goto out_unlock;
    }

    target = hook->original;
    if (!target)
        target = ksu_resolve_symbol_for_functable_hook(target_name);
    if (!target) {
        pr_err("lsm_hook: failed to resolve target for %s\n", hook->head_name ?: "unknown");
        ret = -ENOENT;
        goto out_unlock;
    }
    SUSFS_LOGI("target: 0x%lx %pSb\n", (unsigned long)target, target);

#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 12, 0)
    if (!scalls_addr) {
        scalls_addr = find_kernel_symbol_exact("static_calls_table");
    }
    if (!scalls_addr) {
        pr_err("lsm_hook: failed to resolve static_calls_table\n");
        ret = -ENOSYS;
        goto out_unlock;
    }

    if (scalls_count == 0) {

        unsigned long sym_size = sizeof(struct lsm_static_calls_table);
        unsigned long addr = find_kernel_symbol_exact("lsm_active_cnt");

        if (addr)
            SUSFS_LOGI("lsm_active_cnt = %d (only informational; the table stride is %d)\n",
                    (int)*(u32 *)addr, (int)KSU_LSM_SLOTS_PER_HOOK);

        if (sym_size % (KSU_LSM_SLOTS_PER_HOOK * sizeof(struct lsm_static_call)) != 0) {
            pr_warn("lsm_hook: static_calls_table is %lu bytes, not a whole number of %d-slot hooks\n",
                    sym_size, (int)KSU_LSM_SLOTS_PER_HOOK);
        }
        scalls_count = sym_size / sizeof(struct lsm_static_call);
        SUSFS_LOGI("scalls_count = %zu\n", scalls_count);
    }

    if (scalls_count == 0) {
        pr_err("no scalls_count found!\n");
        ret = -ENOSYS;
        goto out_unlock;
    }

    scalls = (struct lsm_static_call *)scalls_addr;
    for (i = 0; i < scalls_count; i++) {
        struct lsm_static_call *scall = &scalls[i];
        void **slot;
        void *current_origin;

        entry = READ_ONCE(scall->hl);
        if (!entry)
            continue;

        slot = (void **)((char *)entry + hook->hook_offset);
        current_origin = READ_ONCE(*slot);

        int j;
        for (j = 0; j < ksu_lsm_hook_count; j++) {
            if (ksu_lsm_hook_entries[j].hook->replacement == current_origin) {
                current_origin = ksu_lsm_hook_entries[j].hook->original;
                break;
            }
        }

        if (current_origin == hook->replacement) {
            ret = -EALREADY;
            goto out_unlock;
        }

        if (current_origin != target) {
            continue;
        }

        SUSFS_LOGI("found slot %ld orig %pSb\n", i, current_origin);

        if (!hook->offset) {
            selected_entry = entry;
            selected_scall = scall;
            selected_slot = slot;
            selected_origin = current_origin;
        } else {
            size_t hook_idx = (i / KSU_LSM_SLOTS_PER_HOOK + hook->offset) * KSU_LSM_SLOTS_PER_HOOK;
            if (hook_idx >= scalls_count) {
                pr_err("last lsm hook reached\n");
                ret = -EINVAL;
                goto out_unlock;
            }
            scall = &scalls[hook_idx];
            entry = READ_ONCE(scall->hl);
            if (entry) {
                slot = (void **)((char *)entry + hook->hook_offset);
                current_origin = READ_ONCE(*slot);
            } else {
                current_origin = NULL;
            }
            SUSFS_LOGI("found real slot %ld orig %pSb\n", i, current_origin);

            if (current_origin == hook->replacement) {
                ret = -EALREADY;
                goto out_unlock;
            }
            selected_entry = entry;
            selected_scall = scall;
            selected_slot = slot;
            selected_origin = current_origin;
        }
        break;
    }

    if (!selected_scall) {
        pr_err("lsm_hook: target %s not found in head %s\n", target_name, hook->head_name ?: "unknown");
        ret = -ENOENT;
        goto out_unlock;
    }

    ret = ksu_lsm_hook_track(hook);
    if (ret) {
        pr_err("lsm_hook: too many hooks to track: %d\n", ret);
        goto out_unlock;
    }

    if (ksu_lsm_hook_patch_slot(selected_slot, hook->replacement)) {
        pr_err("lsm_hook: failed to patch %s\n", hook->head_name ?: "unknown");
        ret = -EFAULT;
        goto out_untrack;
    }

    hook->entry = selected_entry;
    hook->scall = selected_scall;
    hook->original = selected_origin;
    smp_wmb();

    if (ksu_lsm_hook_update_scall(selected_scall, hook->replacement)) {

        hook->entry = NULL;
        hook->scall = NULL;
        hook->original = NULL;
        if (ksu_lsm_hook_patch_slot(selected_slot, selected_origin)) {
            pr_err("lsm_hook: failed to roll back %s after static call update failure\n", hook->head_name ?: "unknown");
        }
        ret = -EFAULT;
        goto out_untrack;
    }

    if (!selected_origin)
        static_branch_enable(selected_scall->active);

    SUSFS_LOGI("lsm_hook: patched %s hook slot %px from %px to %px\n", hook->head_name ?: "unknown", selected_slot,
            selected_origin, hook->replacement);
#else
    heads_addr = find_kernel_symbol_exact("security_hook_heads");
    if (!heads_addr) {
        pr_err("lsm_hook: failed to resolve security_hook_heads\n");
        ret = -ENOENT;
        goto out_unlock;
    }
    unsigned long heads_size = sizeof(struct security_hook_heads);

    head = (struct hlist_head *)heads_addr;
    struct hlist_head *head_end = (struct hlist_head *)(heads_addr + heads_size);
    SUSFS_LOGI("heads_addr 0x%lx head_offset 0x%lx heads_size %ld hook_offset 0x%lx\n", (unsigned long)heads_addr,
            hook->head_offset, heads_size, hook->hook_offset);

    for (; head < head_end; head++) {
        hlist_for_each_entry (entry, head, list) {
            void **slot = (void **)((char *)entry + hook->hook_offset);
            void *current_origin = READ_ONCE(*slot);
            int j;
            for (j = 0; j < ksu_lsm_hook_count; j++) {
                if (ksu_lsm_hook_entries[j].hook->replacement == current_origin) {
                    current_origin = ksu_lsm_hook_entries[j].hook->original;
                    break;
                }
            }
            if (current_origin == hook->replacement) {
                ret = -EALREADY;
                goto out_unlock;
            }
            if (current_origin == target) {
                SUSFS_LOGI("found %s (target %s) at head offset %ld (provided %ld)\n", hook->head_name, hook->target_name,
                        (unsigned long)head - heads_addr, hook->head_offset);
                selected_entry = entry;
                selected_slot = slot;
                selected_origin = current_origin;
                break;
            }
        }
        if (selected_entry) {
            if (hook->offset) {
                head += hook->offset;
                if (head < (struct hlist_head *)heads_addr || head >= head_end) {
                    pr_err("invalid offset\n");
                    ret = -EINVAL;
                    goto out_unlock;
                }
                hlist_for_each_entry (entry, head, list) {
                    void **slot = (void **)((char *)entry + hook->hook_offset);
                    void *current_origin = READ_ONCE(*slot);
                    if (current_origin == hook->replacement) {
                        ret = -EALREADY;
                        goto out_unlock;
                    }
                }
                if (head->first) {
                    selected_entry = hlist_entry(head->first, struct security_hook_list, list);
                    selected_slot = (void **)((char *)selected_entry + hook->hook_offset);
                    selected_origin = *selected_slot;
                } else {
                    selected_entry = &hook->list;
                    hook->list.head = head;
                    hook->list.list.next = NULL;
                    hook->list.list.pprev = &head->first;
                    hook->list.lsm = "ksu";
                    *(void **)((char *)selected_entry + hook->hook_offset) = hook->replacement;
                    selected_slot = (void **)&head->first;
                    selected_origin = NULL;
                }
            }
            break;
        }
    }

    if (!selected_entry) {
        pr_err("lsm_hook: target %s not found in head %s\n", target_name, hook->head_name ?: "unknown");
        ret = -ENOENT;
        goto out_unlock;
    }

    ret = ksu_lsm_hook_track(hook);
    if (ret) {
        pr_err("lsm_hook: too many hooks to track: %d\n", ret);
        goto out_unlock;
    }

    if (selected_origin) {
        SUSFS_LOGI("patch func addr\n");
        ret = ksu_lsm_hook_patch_slot(selected_slot, hook->replacement);
    } else {
        SUSFS_LOGI("patch head->first\n");
        ret = ksu_lsm_hook_patch_slot(selected_slot, &hook->list);
    }

    if (ret) {
        pr_err("lsm_hook: failed to patch %s\n", hook->head_name ?: "unknown");
        ret = -EFAULT;
        goto out_untrack;
    }

    hook->entry = selected_entry;
    hook->original = selected_origin;
    SUSFS_LOGI("lsm_hook: patched %s hook slot %px from %px to %px\n", hook->head_name ?: "unknown", selected_slot,
            selected_origin, hook->replacement);
#endif
    goto out_unlock;
out_untrack:
    ksu_lsm_hook_untrack(hook);

out_unlock:
    mutex_unlock(&ksu_lsm_hook_lock);
    return ret;
}

void ksu_lsm_unhook(struct ksu_lsm_hook *hook)
{
    void **slot;
    mutex_lock(&ksu_lsm_hook_lock);

#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 12, 0)
    if (!hook->entry || !hook->scall) {
        mutex_unlock(&ksu_lsm_hook_lock);
        return;
    }
    if (hook->insert) {

        if (ksu_lsm_hook_update_scall(hook->scall, hook->original)) {
            pr_err("lsm_hook: failed to restore the static call for %s\n", hook->head_name ?: "unknown");
            mutex_unlock(&ksu_lsm_hook_lock);
            return;
        }
        SUSFS_LOGI("lsm_hook: insert static call slot (selinux) for %s restored to %px\n",
                hook->head_name ?: "unknown", hook->original);
    } else {
        slot = (void **)((char *)hook->entry + hook->hook_offset);
        if (ksu_lsm_hook_patch_slot(slot, hook->original)) {
            pr_err("lsm_hook: failed to restore %s\n", hook->head_name ?: "unknown");
            mutex_unlock(&ksu_lsm_hook_lock);
            return;
        }
        if (ksu_lsm_hook_update_scall(hook->scall, hook->original)) {
            if (ksu_lsm_hook_patch_slot(slot, hook->replacement))
                pr_err("lsm_hook: failed to reapply %s after static call restore failure\n", hook->head_name ?: "unknown");
            mutex_unlock(&ksu_lsm_hook_lock);
            return;
        }
        SUSFS_LOGI("lsm_hook: restored %s hook slot %px to %px\n", hook->head_name ?: "unknown", slot, hook->original);
    }
#else
    if (!hook->entry) {
        mutex_unlock(&ksu_lsm_hook_lock);
        return;
    }

    if (hook->entry == &hook->list) {

        if (ksu_lsm_hook_remove_head(hook)) {
            mutex_unlock(&ksu_lsm_hook_lock);
            return;
        }
    } else {
        slot = (void **)((char *)hook->entry + hook->hook_offset);
        SUSFS_LOGI("unhook patch slot\n");
        if (ksu_lsm_hook_patch_slot(slot, hook->original)) {
            pr_err("lsm_hook: failed to restore %s\n", hook->head_name ?: "unknown");
            mutex_unlock(&ksu_lsm_hook_lock);
            return;
        }
        SUSFS_LOGI("lsm_hook: restored %s hook slot %px to %px\n", hook->head_name ?: "unknown", slot, hook->original);
    }
#endif

    ksu_lsm_hook_untrack(hook);
    hook->entry = NULL;
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 12, 0)
    hook->scall = NULL;
#endif
    mutex_unlock(&ksu_lsm_hook_lock);

    ksu_lsm_hook_drain();
}

static void (*ksu_lsm_sync_rcu_tasks_fn)(void);
static bool ksu_lsm_sync_looked_up;

static __nocfi void ksu_lsm_call_drain(void (*fn)(void))
{
    fn();
}

static void ksu_lsm_hook_drain(void)
{
    if (!ksu_lsm_sync_looked_up) {
        ksu_lsm_sync_rcu_tasks_fn =
            (void *)find_kernel_symbol_exact("synchronize_rcu_tasks");
        if (ksu_lsm_sync_rcu_tasks_fn) {
            /* Cache SUCCESS only - caching a failure keeps the 50 ms fallback forever. */
            ksu_lsm_sync_looked_up = true;
        } else {
            pr_warn("lsm_hook: synchronize_rcu_tasks not found, using a delay\n");
        }
    }

    synchronize_rcu();
    if (ksu_lsm_sync_rcu_tasks_fn)
        ksu_lsm_call_drain(ksu_lsm_sync_rcu_tasks_fn);
    else
        msleep(50);
}

int ksu_register_lsm_hook(struct ksu_lsm_hook *hook)
{
    return ksu_lsm_hook(hook);
}

void ksu_unregister_lsm_hook(struct ksu_lsm_hook *hook)
{
    ksu_lsm_unhook(hook);
}

void ksu_lsm_hook_init(void)
{
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 12, 0)

    ksu_static_call_update_fn = (void *)find_kernel_symbol_exact("__static_call_update");
    SUSFS_LOGI("lsm_hook: static-call switch via %s\n",
            ksu_static_call_update_fn ? "the kernel's __static_call_update() symbol" :
            "the compiled-in __static_call_update() (no such symbol on this kernel)");
#endif
    SUSFS_LOGI("lsm_hook: init, tracked hooks=%d\n", READ_ONCE(ksu_lsm_hook_count));
}

void ksu_lsm_hook_exit(void)
{
    struct ksu_lsm_hook *hooks[ARRAY_SIZE(ksu_lsm_hook_entries)];
    int count;
    int i;

    mutex_lock(&ksu_lsm_hook_lock);
    count = ksu_lsm_hook_count;
    for (i = 0; i < count; i++)
        hooks[i] = ksu_lsm_hook_entries[i].hook;
    mutex_unlock(&ksu_lsm_hook_lock);

    for (i = count - 1; i >= 0; i--)
        ksu_lsm_unhook(hooks[i]);
}
