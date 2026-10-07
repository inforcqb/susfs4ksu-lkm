// SPDX-License-Identifier: GPL-2.0

/* Refuse to load when the imported symbol addresses were not filled in.
 *
 * Every symbol this module imports is a strong SHN_UNDEF entry, and the kernel cannot resolve
 * most of them: they are not in its export table (kallsyms_lookup_name, saved_boot_config,
 * init_mm, ...) or they are namespaced (kern_path, ihold, ...).  They arrive resolved only when
 * the image is rewritten before it reaches the kernel - `ksud insmod` and the bundled
 * susfs_insmod walk the symbol table and turn each SHN_UNDEF into SHN_ABS with the address
 * kallsyms has for that name.
 *
 * A plain `insmod` therefore fails on the first unresolvable name (which is fine - it never
 * runs).  The case worth defending against is a loader that cannot find a name and continues
 * with the value it had, i.e. zero.  What the kernel does with that zero splits the names below
 * in two, and the split is not the same on every variant (measured per artifact, by aggregating
 * every relocation that targets an imported name):
 *
 *   - Most of them are reached by module code through a PC-relative relocation - 49 of the 53 in
 *     the LLVM-CFI builds (5.10/5.15), 45 in the kCFI builds (6.1+).  Zeroing one of those
 *     overflows its relocation, so the kernel refuses the image itself (-ENOEXEC, "overflow in
 *     relocation type 275 val 0") before init_module() is reached.  Nothing to catch.
 *   - The rest are reached only through function or data pointers and are referenced by
 *     R_AARCH64_ABS64 alone, so the kernel accepts a zero in silence: param_ops_bool/int/string/
 *     ulong, plus single_release, seq_read, seq_lseek and delayed_work_timer_fn on the kCFI
 *     builds.  The floor check below is the only line of defence for those - and for the four
 *     param_ops_* it is a weak one, because no check in this module can undo the damage: the
 *     kernel frees a module whose init returned non-zero through free_module() ->
 *     destroy_params(), which reads params->ops->free without testing ops for NULL (measured on a
 *     5.15 GKI build: Oops at +0x18 of struct kernel_param_ops, and a reboot where panic_on_oops
 *     is set).  Loading without refusing is no better - reading or writing the parameter, and
 *     unloading the module, take the same NULL ops path.  Refusing a zeroed pointer out of
 *     file_operations / seq_operations / delayed_work has no such problem: that load simply fails.
 *
 * So: check that every import below has a plausible kernel address before anything else in
 * init runs.  For the param_ops_* case the check can only name the cause in the log before the
 * kernel faults; for every other name it is what actually stops the load.  What keeps them all
 * filled is the loaders, plus the build-time assertion of every import against the target
 * kernel's System.map.
 * Only names present in every variant's import list are listed here - a name a variant does not
 * import would turn this guard itself into a new unresolved symbol. */

#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/init.h>
#include <linux/delay.h>
#include <linux/kstrtox.h>
#include <linux/string.h>
#include <linux/slab.h>
#include <linux/mm.h>
#include <linux/fs.h>
#include <linux/namei.h>
#include <linux/uaccess.h>
#include <linux/mutex.h>
#include <linux/spinlock.h>
#include <linux/rcupdate.h>
#include <linux/kprobes.h>
#include <linux/ratelimit.h>
#include <linux/tracepoint.h>
#include <linux/stop_machine.h>
#include <linux/task_work.h>
#include <linux/workqueue.h>
#include <linux/security.h>
#include <linux/cred.h>
#include <linux/proc_fs.h>
#include <linux/seq_file.h>
#include <linux/moduleparam.h>
#include <asm/fixmap.h>
#include <asm/memory.h>
#include <trace/events/syscalls.h>
#include "susfs.h"
#include "susfs_log.h"
#include "symbol_resolver.h"

/* The variable the bootconfig spoof republishes; nothing declares it in a header. */
extern char *saved_boot_config;

struct susfs_import {
    const char *name;
    const void *addr;
    /* Whether &name is the address the loader wrote into the symbol.  It is for data symbols.
     * For functions it is not, on the LLVM-CFI builds (5.10/5.15): there &f in a data initializer
     * resolves to a module-local long-branch stub, so only the objects below are cross-checked.
     * The kCFI builds (6.1/6.6) resolve &f to the loader's address for all 53 entries, so the same
     * check could cover them too; it stays off until a 6.1/6.6 device confirms it, because a wrong
     * comparison here refuses a good load. */
    bool compare;
};

/* Address of the symbol itself, not of what it points at: the loader fills the former. */
#define IMP(n) { #n, (const void *)&n, false }
#define IMP_DATA(n) { #n, (const void *)&n, true }

static const struct susfs_import susfs_imports[] = {
    /* names the loaders exist for: unexported or namespaced */
    IMP_DATA(saved_boot_config),
    IMP_DATA(init_mm),
    IMP(kern_path),
    IMP(ihold),
    IMP(iput),
    IMP(path_put),
    IMP(task_work_add),
    IMP(__set_fixmap),
    IMP_DATA(memstart_addr),
    IMP_DATA(arm64_use_ng_mappings),
    IMP(copy_to_kernel_nofault),
    IMP(security_secctx_to_secid),
    IMP(stop_machine),
    IMP_DATA(__tracepoint_sys_exit),
    IMP(tracepoint_probe_register),
    IMP(tracepoint_probe_unregister),
    IMP(register_kprobe),
    IMP(unregister_kprobe),
    IMP(register_kretprobe),
    IMP(unregister_kretprobe),
    IMP_DATA(param_ops_bool),
    IMP_DATA(param_ops_int),
    IMP_DATA(param_ops_string),
    IMP_DATA(param_ops_ulong),
    /* the control nodes and their readers */
    IMP(proc_create),
    IMP(proc_remove),
    IMP(single_open),
    IMP(single_release),
    IMP(seq_printf),
    IMP(seq_read),
    IMP(seq_write),
    IMP(seq_lseek),
    IMP(kstrdup),
    IMP(kstrtoll),
    IMP_DATA(kmalloc_caches),
    IMP(mutex_lock),
    IMP(mutex_trylock),
    IMP(mutex_unlock),
    IMP(_raw_spin_lock),
    IMP(_raw_spin_lock_irqsave),
    IMP(_raw_spin_unlock),
    IMP(_raw_spin_unlock_irqrestore),
    IMP(__rcu_read_lock),
    IMP(__rcu_read_unlock),
    IMP(__put_cred),
    IMP(strnlen_user),
    IMP(___ratelimit),
    IMP(__check_object_size),
    IMP(queue_delayed_work_on),
    IMP(cancel_delayed_work_sync),
    IMP(delayed_work_timer_fn),
    IMP(synchronize_rcu),
    IMP(msleep),
};

/* arm64 user and kernel space cannot overlap: every kernel text/data/vmalloc address on a
 * GKI build sits far above this, and a zero-filled or user-space value sits below it.
 * How much of the table this really covers depends on the variant: the 43 function entries hold a
 * module-local stub address in the LLVM-CFI builds (always above the floor, so only the 10 data
 * entries are checked there), and the loader's address in the kCFI builds (all 53 are checked). */
#define SUSFS_IMPORT_ADDR_MIN 0xff00000000000000UL

int susfs_imports_guard(void)
{
    unsigned int i, bad = 0;
    bool ops_missing = false;
    const char *first = NULL, *second = NULL, *third = NULL;

    for (i = 0; i < ARRAY_SIZE(susfs_imports); i++) {
        unsigned long a = (unsigned long)susfs_imports[i].addr;

        if (a >= SUSFS_IMPORT_ADDR_MIN)
            continue;
        bad++;
        if (!strncmp(susfs_imports[i].name, "param_ops_", 10))
            ops_missing = true;
        if (!first)
            first = susfs_imports[i].name;
        else if (!second)
            second = susfs_imports[i].name;
        else if (!third)
            third = susfs_imports[i].name;
    }

    if (!bad)
        return 0;

    pr_err("susfs_guard_lkm: %u of %u imported symbol(s) have no kernel address (%s%s%s%s) - this image was not absolutized before init_module(). Load it with `ksud insmod` or the bundled `susfs_insmod`, not with a plain `insmod` (or with a loader that continues after an unresolved name): the kernel accepts a zero address here without complaining, and the first call through it jumps to 0. Refusing to load.\n",
           bad, (unsigned int)ARRAY_SIZE(susfs_imports), first ? first : "?",
           second ? ", " : "", second ? second : "", third ? ", ..." : "");
    if (ops_missing)
        pr_err("susfs_guard_lkm: note: the names include a param_ops_*, so refusing is not enough to keep this load attempt alive - the kernel frees this module through destroy_params(), which reads ops->free with a NULL ops, and faults. This message is the reason that fault is coming.\n");
    return -EINVAL;
}

/* The second half, called once the symbol resolver is up.  Every image that reaches init has been
 * through the kernel's relocation step, but that only proves an address is non-zero, not that it is
 * the right one.  What can load and still be wrong is a plausibly-valued address that belongs to
 * the wrong symbol - a stale kallsyms snapshot, or the wrong occurrence of a name that kallsyms
 * lists more than once.  For the data symbols this comparison is exact (&name IS the address the
 * loader wrote, measured: patching init_mm to another kernel address shows up here as that
 * address); for functions it is not - see the compare field above. */
int susfs_imports_crosscheck(void)
{
    unsigned long addrs[2];
    unsigned int i, bad = 0, skipped = 0;

    for (i = 0; i < ARRAY_SIZE(susfs_imports); i++) {
        int n;

        if (!susfs_imports[i].compare)
            continue;
        n = ksu_find_symbol_all(susfs_imports[i].name, addrs, 2);

        /* 0 = this kernel does not have the name (or the resolver could not be bootstrapped),
         * 2 = the name is ambiguous; in both cases there is nothing to compare against. */
        if (n != 1) {
            skipped++;
            continue;
        }
        if (addrs[0] == (unsigned long)susfs_imports[i].addr)
            continue;

        bad++;
        if (bad <= 3)
            pr_err("susfs_guard_lkm: import %s = 0x%lx but kallsyms has 0x%lx\n",
                   susfs_imports[i].name, (unsigned long)susfs_imports[i].addr, addrs[0]);
    }

    if (skipped)
        pr_warn("susfs_guard_lkm: %u import(s) were not cross-checked: this kernel's kallsyms has no such name, lists it more than once, or the resolver is not up\n",
                skipped);

    if (!bad)
        return 0;

    pr_err("susfs_guard_lkm: %u imported data symbol(s) do not match this kernel's kallsyms - the image was absolutized from the wrong symbol table (a stale /proc/kallsyms, or the wrong occurrence of a name that appears more than once). Load it with `ksud insmod` or the bundled `susfs_insmod` and reload; refusing to load.\n",
           bad);
    return -EINVAL;
}
