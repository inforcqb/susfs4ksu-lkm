// SPDX-License-Identifier: GPL-2.0

#include <linux/module.h>
#include <linux/kprobes.h>
#include <linux/fs.h>
#include <linux/mm.h>		/* struct mm_struct; sus_map_find_vma() walks its vmas */
#include <linux/mm_types.h>
#include <linux/version.h>	/* LINUX_VERSION_CODE: mm->mmap vs mm->mm_mt (6.1) */
#include <linux/namei.h>
#include <linux/dcache.h>
#include <linux/uaccess.h>
#include <linux/err.h>		/* IS_ERR/ERR_PTR for the getlink hook */
#include <linux/cred.h>		/* current_uid(), for the read gate */
#include <linux/spinlock.h>	/* serialises rule publication */
#include "susfs_abi.h"
#include "susfs_log.h"
#include "susfs.h"	/* susfs_abi_path_ok */
#include "symbol_resolver.h"	/* find_kernel_symbol_exact, for the walk ops */
#include "ksu_umount_gate.h"	/* susfs_is_current_proc_umounted_app (issue #34) */

#define SUS_MAP_MAX 64

struct sus_map_entry {
    unsigned long target_ino;
    dev_t target_dev;
};

static struct sus_map_entry map_entries[SUS_MAP_MAX];
static int nmap;

static DEFINE_SPINLOCK(map_table_lock);

/* temporary interface: insmod susfs_guard_lkm.ko map_ino=<n> hides that inode */
static unsigned long param_map_ino;
module_param_named(map_ino, param_map_ino, ulong, 0644);

/* dev==0 means "any filesystem": only the map_ino parameter can pick that. */
static int sus_map_add_full(unsigned long ino, dev_t dev)
{
    unsigned long flags;
    int rc = 0;

    if (!ino)
        return -EINVAL;

    spin_lock_irqsave(&map_table_lock, flags);
    if (nmap < SUS_MAP_MAX) {
        map_entries[nmap].target_ino = ino;
        map_entries[nmap].target_dev = dev;
        smp_store_release(&nmap, nmap + 1);
    } else {
        rc = -ENOSPC;
    }
    spin_unlock_irqrestore(&map_table_lock, flags);
    return rc;
}

static void sus_map_add(unsigned long ino)
{
    sus_map_add_full(ino, 0);
}

static bool sus_map_lookup(unsigned long ino, dev_t dev)
{
    int n = smp_load_acquire(&nmap);
    int i;

    for (i = 0; i < n; i++) {
        if (map_entries[i].target_ino != ino)
            continue;
        if (map_entries[i].target_dev && map_entries[i].target_dev != dev)
            continue;
        return true;
    }
    return false;
}

/* Upstream's read gate is SUSFS_IS_INODE_SUS_MAP() -> susfs_is_current_proc_umounted_app(): apps
 * only, and only the ones KernelSU umounts modules for, so root/init and a su-granted app see the
 * real mapping.  The plain `uid >= 10000` proxy this replaces hid from the manager and from
 * su-granted apps too (issue #34).  Configuration stays ungated: the supercall and map_ino are rule
 * management. */
static bool sus_map_gate_ok(void)
{
    return susfs_is_current_proc_umounted_app();
}

static int sus_map_skip_vma_pre(struct kprobe *kp, struct pt_regs *regs)
{
    struct vm_area_struct *vma;
    struct inode *inode;

    if (!sus_map_gate_ok())
        return 0;

    vma = (struct vm_area_struct *)regs->regs[1];

    if ((unsigned long)vma < PAGE_SIZE)
        return 0;
    if (!vma->vm_file)
        return 0;
    inode = file_inode(vma->vm_file);
    if (!inode)
        return 0;
    if (sus_map_lookup(inode->i_ino, inode->i_sb->s_dev)) {
        /* ratelimited like sus_path's; the rule stores no path, so ino/dev name it */
        pr_info_ratelimited("sus_map: hid %s line (ino=%lu dev=%lu uid=%u)\n",
                            kp->symbol_name, inode->i_ino,
                            (unsigned long)inode->i_sb->s_dev,
                            current_uid().val);
        regs_set_return_value(regs, 0);
        regs->pc = regs->regs[30];
        return 1;
    }
    return 0;
}

static struct kprobe kp_map = {
    .symbol_name = "show_map_vma",
    .pre_handler = sus_map_skip_vma_pre,
};

static struct kprobe kp_map_smap = {
    .symbol_name = "show_smap",
    .pre_handler = sus_map_skip_vma_pre,
};

static const void *sus_map_ops_smaps;
static const void *sus_map_ops_smaps_shmem;
static const void *sus_map_ops_pagemap;
static bool sus_map_walk_ops_done;
static atomic_t n_walk_skip = ATOMIC_INIT(0);
static atomic_t n_walk_seen = ATOMIC_INIT(0);		/* walk_page_range calls */
static atomic_t n_walk_seen_vma = ATOMIC_INIT(0);	/* walk_page_vma calls  */
/* One counter per resolution step: "the walk was not skipped" has four different causes. */
static atomic_t n_walk_ops_hit = ATOMIC_INIT(0);	/* ops was ours */
static atomic_t n_walk_scan_fail = ATOMIC_INIT(0);	/* no vma for (mm,start) */
static atomic_t n_walk_nofile = ATOMIC_INIT(0);		/* vma has no vm_file */
static atomic_t n_walk_nomatch = ATOMIC_INIT(0);	/* inode is not a rule */
static atomic_t n_walk_dbg_left = ATOMIC_INIT(4);

static atomic_t n_map_files_hides = ATOMIC_INIT(0);
static atomic_t n_getlink_calls = ATOMIC_INIT(0);
static atomic_t n_getlink_skip = ATOMIC_INIT(0);
static atomic_t n_getlink_nomatch = ATOMIC_INIT(0);

/* walk_dbg: name every ops pointer reaching the two primitives, once per value (off by default - a linear scan per call). */
static int walk_dbg;
module_param_named(walk_dbg, walk_dbg, int, 0644);

#define WALK_OPS_MAX 8
static const void *walk_seen_ops[WALK_OPS_MAX];
static atomic_t walk_seen_cnt[WALK_OPS_MAX];
static int walk_seen_n;

static void sus_map_note_ops(const void *ops)
{
    int i, n = READ_ONCE(walk_seen_n);

    for (i = 0; i < n; i++) {
        if (READ_ONCE(walk_seen_ops[i]) == ops) {
            atomic_inc(&walk_seen_cnt[i]);
            return;
        }
    }
    if (n >= WALK_OPS_MAX)
        return;
    WRITE_ONCE(walk_seen_ops[n], ops);
    atomic_inc(&walk_seen_cnt[n]);
    smp_store_release(&walk_seen_n, n + 1);
    SUSFS_LOGI("sus_map: walk ops[%d] = %pS\n", n, ops);
}

static int sus_map_walk_ops_show(char *buf, const struct kernel_param *kp)
{
    int i, n = 0, cnt = READ_ONCE(walk_seen_n);

    for (i = 0; i < cnt; i++)
        n += scnprintf(buf + n, PAGE_SIZE - n, "%2d %pS\n", i, walk_seen_ops[i]);
    n += scnprintf(buf + n, PAGE_SIZE - n,
                   "counts: page_range=%d page_vma=%d skipped=%d\n",
                   atomic_read(&n_walk_seen), atomic_read(&n_walk_seen_vma),
                   atomic_read(&n_walk_skip));
    for (i = 0; i < cnt; i++)
        n += scnprintf(buf + n, PAGE_SIZE - n, "  [%d] n=%d\n", i,
                       atomic_read(&walk_seen_cnt[i]));
    return n;
}
static const struct kernel_param_ops sus_map_walk_ops_ops = {
    .get = sus_map_walk_ops_show,
};
module_param_cb(walk_ops, &sus_map_walk_ops_ops, NULL, 0400);

static void sus_map_resolve_walk_ops(void)
{
    if (sus_map_walk_ops_done)
        return;
    sus_map_walk_ops_done = true;

    sus_map_ops_smaps = (const void *)find_kernel_symbol_exact("smaps_walk_ops");
    sus_map_ops_smaps_shmem = (const void *)find_kernel_symbol_exact("smaps_shmem_walk_ops");
    sus_map_ops_pagemap = (const void *)find_kernel_symbol_exact("pagemap_ops");

    if (!sus_map_ops_smaps && !sus_map_ops_smaps_shmem && !sus_map_ops_pagemap) {
        pr_warn("sus_map: smaps/pagemap walk ops not found in kallsyms - "
                "smaps_rollup and pagemap stay unfiltered\n");
        return;
    }
    SUSFS_LOGI("sus_map: walk ops smaps=%px smaps_shmem=%px pagemap=%px\n",
            sus_map_ops_smaps, sus_map_ops_smaps_shmem, sus_map_ops_pagemap);
}

static bool sus_map_walk_ops_any(void)
{
    return sus_map_ops_smaps || sus_map_ops_smaps_shmem || sus_map_ops_pagemap;
}

static bool sus_map_walk_ops_ours(const void *ops)
{
    return ops && (ops == sus_map_ops_smaps || ops == sus_map_ops_smaps_shmem ||
                   ops == sus_map_ops_pagemap);
}

static bool sus_map_walk_answer(struct kprobe *kp, struct pt_regs *regs,
                                struct vm_area_struct *vma)
{
    struct inode *inode;

    /* Defence in depth, like the vma handler: a real vma is never below a page. */
    if ((unsigned long)vma < PAGE_SIZE)
        return false;
    if (!vma->vm_file) {
        atomic_inc(&n_walk_nofile);
        return false;
    }
    inode = file_inode(vma->vm_file);
    if (!inode) {
        atomic_inc(&n_walk_nofile);
        return false;
    }
    if (!sus_map_lookup(inode->i_ino, inode->i_sb->s_dev)) {
        atomic_inc(&n_walk_nomatch);
        return false;
    }

    atomic_inc(&n_walk_skip);
    pr_info_ratelimited("sus_map: skipped %s walk for ino=%lu dev=%lu uid=%u\n",
                        kp->symbol_name, inode->i_ino,
                        (unsigned long)inode->i_sb->s_dev, current_uid().val);

    regs_set_return_value(regs, 0);
    regs->pc = regs->regs[30];
    return true;
}

static struct vm_area_struct *sus_map_find_vma(struct mm_struct *mm, unsigned long start)
{
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 1, 0)
	struct vm_area_struct *vma;
	VMA_ITERATOR(vmi, mm, 0);

	for_each_vma(vmi, vma) {
		if (start < vma->vm_end)
			return vma;
	}
	return NULL;
#else
	struct vm_area_struct *vma;

	for (vma = mm->mmap; vma; vma = vma->vm_next) {
		if (start < vma->vm_end)
			break;
	}
	return vma;
#endif
}

static void sus_map_walk_dbg_log(const char *what, struct mm_struct *mm,
                                 unsigned long start, struct vm_area_struct *vma)
{
    if (walk_dbg < 2)
        return;
    if (atomic_dec_if_positive(&n_walk_dbg_left) < 0)
        return;
    SUSFS_LOGI("sus_map: %s mm=%px start=%lx mmap=%px vma=%px %lx-%lx file=%px\n",
            what, mm, start, mm ? sus_map_find_vma(mm, 0) : NULL, vma,
            vma ? vma->vm_start : 0UL, vma ? vma->vm_end : 0UL,
            (vma && vma->vm_file) ? vma->vm_file : NULL);
}

static int sus_map_skip_walk_pre(struct kprobe *kp, struct pt_regs *regs)
{
    const void *ops = (const void *)regs->regs[3];
    struct mm_struct *mm;
    struct vm_area_struct *vma;
    unsigned long start;

    atomic_inc(&n_walk_seen);
    if (walk_dbg)
        sus_map_note_ops(ops);
    if (!sus_map_walk_ops_ours(ops))
        return 0;

    atomic_inc(&n_walk_ops_hit);
    if (!sus_map_gate_ok())
        return 0;

    mm = (struct mm_struct *)regs->regs[0];
    start = (unsigned long)regs->regs[1];
    if (!mm)
        return 0;

    vma = sus_map_find_vma(mm, start);
    if (!vma || start < vma->vm_start) {
        atomic_inc(&n_walk_scan_fail);
        sus_map_walk_dbg_log("walk_page_range: no vma", mm, start, NULL);
        return 0;
    }
    sus_map_walk_dbg_log("walk_page_range: vma", mm, start, vma);

    return sus_map_walk_answer(kp, regs, vma) ? 1 : 0;
}

/* walk_page_vma(vma, ops, private): same walk, vma handed over directly. */
static int sus_map_skip_walk_vma_pre(struct kprobe *kp, struct pt_regs *regs)
{
    const void *ops = (const void *)regs->regs[1];

    atomic_inc(&n_walk_seen_vma);
    if (walk_dbg)
        sus_map_note_ops(ops);
    if (!sus_map_walk_ops_ours(ops))
        return 0;

    atomic_inc(&n_walk_ops_hit);
    if (!sus_map_gate_ok())
        return 0;

    return sus_map_walk_answer(kp, regs,
                               (struct vm_area_struct *)regs->regs[0]) ? 1 : 0;
}

static struct kprobe kp_map_walk = {
    .symbol_name = "walk_page_range",
    .pre_handler = sus_map_skip_walk_pre,
};

static struct kprobe kp_map_walk_vma = {
    .symbol_name = "walk_page_vma",
    .pre_handler = sus_map_skip_walk_vma_pre,
};

static atomic_t n_gup_calls = ATOMIC_INIT(0);
static atomic_t n_gup_inner_calls = ATOMIC_INIT(0);
static atomic_t n_vm_hides = ATOMIC_INIT(0);

static int sus_map_vm_access_pre(struct kprobe *kp, struct pt_regs *regs);

static struct kprobe kp_gup_remote = {
    .symbol_name = "get_user_pages_remote",
    .pre_handler = sus_map_vm_access_pre,
};

static struct kprobe kp_gup_remote_inner = {
    .symbol_name = "__get_user_pages_remote",
    .pre_handler = sus_map_vm_access_pre,
};

static int sus_map_vm_access_pre(struct kprobe *kp, struct pt_regs *regs)
{
    struct mm_struct *mm = (struct mm_struct *)regs->regs[0];
    unsigned long addr = regs->regs[1];
    struct vm_area_struct *vma;
    struct inode *inode;

    if (!smp_load_acquire(&nmap))
        return 0;
    if (!sus_map_gate_ok())
        return 0;
    if (!mm || !addr)
        return 0;

    atomic_inc(kp == &kp_gup_remote_inner ? &n_gup_inner_calls : &n_gup_calls);

    /* both callers hold mmap_read_lock: the *_remote contract of this primitive */
    vma = find_vma(mm, addr);
    if (!vma || !vma->vm_file)
        return 0;
    inode = file_inode(vma->vm_file);
    if (!inode)
        return 0;
    if (!sus_map_lookup(inode->i_ino, inode->i_sb->s_dev))
        return 0;

    atomic_inc(&n_vm_hides);
    regs_set_return_value(regs, 0);     /* "nothing transferred" */
    regs->pc = regs->regs[30];          /* skip the call: nothing is pinned */
    return 1;
}

static int sus_map_maplink_entry(struct kretprobe_instance *ri, struct pt_regs *regs)
{
    /* struct path *path is an output argument, filled only at return: save it here. */
    *(unsigned long *)ri->data = regs->regs[1];
    return 0;
}

static int sus_map_maplink_ret(struct kretprobe_instance *ri, struct pt_regs *regs)
{
    unsigned long outp = *(unsigned long *)ri->data;
    const struct path *p;
    struct inode *inode;

    atomic_inc(&n_getlink_calls);
    if ((long)regs_return_value(regs) != 0 || !outp) {
        atomic_inc(&n_getlink_skip);
        return 0;
    }
    if (!sus_map_gate_ok()) {
        atomic_inc(&n_getlink_skip);
        return 0;
    }
    p = (const struct path *)outp;
    if (!p->dentry) {
        atomic_inc(&n_getlink_skip);
        return 0;
    }
    inode = d_inode(p->dentry);
    if (!inode) {
        atomic_inc(&n_getlink_skip);
        return 0;
    }
    if (!sus_map_lookup(inode->i_ino, inode->i_sb->s_dev)) {
        atomic_inc(&n_getlink_nomatch);
        return 0;
    }

    atomic_inc(&n_map_files_hides);
    pr_info_ratelimited("sus_map: hid map_files symlink to ino=%lu (uid=%u)\n",
                        inode->i_ino, current_uid().val);
    regs_set_return_value(regs, (unsigned long)(long)-ENOENT);
    return 0;
}

static struct kretprobe kr_map_files = {
    .kp.symbol_name = "map_files_get_link",
    .entry_handler = sus_map_maplink_entry,
    .handler = sus_map_maplink_ret,
    .data_size = sizeof(unsigned long),	/* the output struct path * */
    .maxactive = 16,
};
static bool kr_map_files_ok;

/* Kept in one table so init and exit cannot drift apart. */
static struct kprobe *const map_probes[] = {
    &kp_map, &kp_map_smap, &kp_map_walk, &kp_map_walk_vma,
    &kp_gup_remote, &kp_gup_remote_inner,
};
#define N_MAP_PROBES ARRAY_SIZE(map_probes)
static bool map_registered;
static bool map_probe_armed[N_MAP_PROBES];

static int sus_map_stat_show(char *buf, const struct kernel_param *kp)
{
    int i, armed = 0;

    for (i = 0; i < (int)N_MAP_PROBES; i++)
        armed += map_probe_armed[i] ? 1 : 0;

    return scnprintf(buf, PAGE_SIZE,
                     "rules=%d armed=%d/%d walk_seen=%d walk_vma=%d walk_skipped=%d "
                     "ops_hit=%d scan_fail=%d nofile=%d nomatch=%d getlink: calls=%d skip=%d nomatch=%d hides=%d\n"
                     "vm: gup_calls=%d inner_calls=%d hides=%d\n"
                     "ops: smaps=%px smaps_shmem=%px pagemap=%px\n",
                     nmap, armed, (int)N_MAP_PROBES,
                     atomic_read(&n_walk_seen), atomic_read(&n_walk_seen_vma),
                     atomic_read(&n_walk_skip),
                     atomic_read(&n_walk_ops_hit), atomic_read(&n_walk_scan_fail),
                     atomic_read(&n_walk_nofile), atomic_read(&n_walk_nomatch),
                     atomic_read(&n_getlink_calls), atomic_read(&n_getlink_skip),
                     atomic_read(&n_getlink_nomatch), atomic_read(&n_map_files_hides),
                     atomic_read(&n_gup_calls), atomic_read(&n_gup_inner_calls),
                     atomic_read(&n_vm_hides),
                     sus_map_ops_smaps, sus_map_ops_smaps_shmem,
                     sus_map_ops_pagemap);
}
static const struct kernel_param_ops sus_map_stat_ops = {
    .get = sus_map_stat_show,
};
module_param_cb(map_stat, &sus_map_stat_ops, NULL, 0400);

static int sus_map_register_probes(void)
{
    int i, n = 0, first_err = 0;

    sus_map_resolve_walk_ops();

    for (i = 0; i < (int)N_MAP_PROBES; i++) {
        int rc;

        if (map_probe_armed[i])
            continue;
        if ((map_probes[i] == &kp_map_walk || map_probes[i] == &kp_map_walk_vma) &&
            !sus_map_walk_ops_any())
            continue;
        rc = register_kprobe(map_probes[i]);
        if (rc) {
            pr_warn("sus_map: register_kprobe(%s) failed %d - that listing is not filtered\n",
                    map_probes[i]->symbol_name, rc);
            if (!first_err)
                first_err = rc;
            continue;
        }
        map_probe_armed[i] = true;
        n++;
    }

    if (n)
        SUSFS_LOGI("sus_map: %d/%d probes armed (%d rules)\n",
                n, (int)N_MAP_PROBES, nmap);

    if (!kr_map_files_ok) {
        int rc = register_kretprobe(&kr_map_files);

        if (rc)
            pr_warn("sus_map: register_kretprobe(proc_map_files_get_link) failed %d - readlink on a hidden mapping still names the file\n",
                    rc);
        else
            kr_map_files_ok = true;
    }

    map_registered = map_probe_armed[0];   /* show_map_vma is the required one */
    return map_registered ? 0 : first_err;
}

int susfs_sus_map_init(void)
{
    int rc;

    sus_map_add(param_map_ino);
    if (nmap == 0) {
        SUSFS_LOGI("sus_map: no rules, hook not installed\n");
        return 0;
    }

    rc = sus_map_register_probes();
    if (rc)
        return rc;
    return 0;
}

void susfs_sus_map_exit(void)
{
    int i;

    for (i = 0; i < (int)N_MAP_PROBES; i++) {
        if (!map_probe_armed[i])
            continue;
        unregister_kprobe(map_probes[i]);
        map_probe_armed[i] = false;
    }
    if (kr_map_files_ok) {
        unregister_kretprobe(&kr_map_files);
        kr_map_files_ok = false;
    }
    map_registered = false;
    nmap = 0;
}

/* supercall: CMD_SUSFS_ADD_SUS_MAP (resolve path -> ino/dev, register hook) */
void susfs_sus_map_supercall(void __user **arg)
{
    struct st_susfs_sus_map info = {0};
    struct path p;
    struct inode *inode;
    int rc;

    if (copy_from_user(&info, (void __user *)*arg, sizeof(info))) {
        info.err = -EFAULT;
        goto out;
    }

    /* char[256] field that need not be NUL-terminated: reject it before kern_path() can read off the end of our stack copy. */
    if (!susfs_abi_path_ok(info.target_pathname, sizeof(info.target_pathname))) {
        info.err = -ENAMETOOLONG;
        goto out;
    }

    rc = kern_path(info.target_pathname, LOOKUP_FOLLOW, &p);
    if (rc) {
        info.err = rc;
        goto out;
    }
    inode = d_backing_inode(p.dentry);
    if (!inode) {
        path_put(&p);
        info.err = -ENOENT;
        goto out;
    }

    if (nmap >= SUS_MAP_MAX) {
        path_put(&p);
        info.err = -ENOSPC;
        goto out;
    }

    rc = sus_map_add_full(inode->i_ino, inode->i_sb->s_dev);
    if (rc) {
        path_put(&p);
        info.err = rc;
        goto out;
    }
    SUSFS_LOGI("sus_map: added %s (ino=%lu) via supercall\n",
            info.target_pathname, inode->i_ino);
    path_put(&p);

    if (!map_registered) {
        rc = sus_map_register_probes();
        if (rc) {
            info.err = rc;
            goto out;
        }
    }
    info.err = 0;
out:
    /* upstream writes back only ->err for input-type commands */
    if (copy_to_user(&((struct st_susfs_sus_map __user *)*arg)->err,
                     &info.err, sizeof(info.err)))
        pr_warn("sus_map supercall copy_to_user failed\n");
}
