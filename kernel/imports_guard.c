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
 * with the value it had, i.e. zero: the kernel accepts SHN_ABS/0 without a word, and the first
 * call through that symbol jumps to address 0.  Nothing about that is visible from userspace
 * until it panics.
 *
 * So: check that every import below has a plausible kernel address before anything else in
 * init runs.  Only names present in every variant's import list are listed here - a name a
 * variant does not import would turn this guard itself into a new unresolved symbol. */

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
    /* Whether &name is the address the loader wrote into the symbol.  It is for data symbols,
     * and it is NOT for functions: there, &f in a data initializer resolves to a module-local
     * stub, which is why only the objects below are cross-checked against kallsyms. */
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
 * GKI build sits far above this, and a zero-filled or user-space value sits below it. */
#define SUSFS_IMPORT_ADDR_MIN 0xff00000000000000UL

int susfs_imports_guard(void)
{
    unsigned int i, bad = 0;
    const char *first = NULL, *second = NULL, *third = NULL;

    for (i = 0; i < ARRAY_SIZE(susfs_imports); i++) {
        unsigned long a = (unsigned long)susfs_imports[i].addr;

        if (a >= SUSFS_IMPORT_ADDR_MIN)
            continue;
        bad++;
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
    return -EINVAL;
}

/* The second half, called once the symbol resolver is up.  The floor check above cannot fire on
 * arm64 in practice: an import left at zero is refused by the kernel's own relocation step before
 * init_module() returns (measured: an image with three imports zeroed comes back -ENOEXEC, and the
 * kernel says "overflow in relocation type 275 val 0"), so every image that LOADS has addresses.
 * What can load and still be wrong is a plausibly-valued address that belongs to the wrong symbol -
 * a stale kallsyms snapshot, or the wrong occurrence of a name that kallsyms lists more than once.
 * For the data symbols this comparison is exact (&name IS the address the loader wrote, measured:
 * patching init_mm to another kernel address shows up here as that address); for functions it is
 * not, because &f in a data initializer resolves to a module-local stub, so those are skipped. */
int susfs_imports_crosscheck(void)
{
    unsigned long addrs[2];
    unsigned int i, bad = 0;

    for (i = 0; i < ARRAY_SIZE(susfs_imports); i++) {
        int n;

        if (!susfs_imports[i].compare)
            continue;
        n = ksu_find_symbol_all(susfs_imports[i].name, addrs, 2);

        /* 0 = this kernel does not have the name (or the resolver could not be bootstrapped),
         * 2 = the name is ambiguous; in both cases there is nothing to compare against. */
        if (n != 1)
            continue;
        if (addrs[0] == (unsigned long)susfs_imports[i].addr)
            continue;

        bad++;
        if (bad <= 3)
            pr_err("susfs_guard_lkm: import %s = 0x%lx but kallsyms has 0x%lx\n",
                   susfs_imports[i].name, (unsigned long)susfs_imports[i].addr, addrs[0]);
    }

    if (!bad)
        return 0;

    pr_err("susfs_guard_lkm: %u imported data symbol(s) do not match this kernel's kallsyms - the image was absolutized from the wrong symbol table (a stale /proc/kallsyms, or the wrong occurrence of a name that appears more than once). Load it with `ksud insmod` or the bundled `susfs_insmod` and reload; refusing to load.\n",
           bad);
    return -EINVAL;
}
