// SPDX-License-Identifier: GPL-2.0
/*
 * susfs_kstat.c - spoof kstat fields (SUSFS SUS_KSTAT feature), LKM port.
 *
 * Interface mirrors the original SUSFS userspace commands, one command per write to
 * /proc/susfs_kstat:
 *   add_sus_kstat <path> - store the CURRENT stat of <path> as the spoof target
 *       (ino/dev/times/blocks/blksize), flags = KSTAT_AUTO_SPOOF; use it BEFORE the path is
 *       bind-mounted/overlayed, then call update_sus_kstat.
 *   add_sus_kstat_statically <path> <ino> <dev> <nlink> <size> <atime> <atime_nsec> <mtime>
 *       <mtime_nsec> <ctime> <ctime_nsec> <blocks> <blksize> - set each field explicitly;
 *       "default" keeps the current value and does NOT spoof that field, and only non-default
 *       fields get their KSTAT_SPOOF_* flag set.
 *   update_sus_kstat <path> / update_sus_kstat_full_clone <path> - re-resolve <path> (after it was
 *       bind-mounted/overlayed) and update target_ino/target_dev only, spoofed values staying as
 *       previously added; the _full_clone form also raises KSTAT_SPOOF_NLINK|KSTAT_SPOOF_SIZE.
 *   del <path> - remove one rule by its target pathname;   clear - remove all rules.
 *
 * Hook strategy (LTO on this GKI inlines the newfstatat chain vfs_fstatat -> vfs_statx ->
 * vfs_getattr -> cp_new_stat, so VFS-layer kprobes miss): the reliable hook is the return of
 * __arm64_sys_newfstatat, where the user statbuf is fully written.  Rewrite the requested fields
 * there via copy_to_user.  Field offsets are arm64 asm-generic struct stat.
 */
#include <linux/module.h>
#include <linux/kprobes.h>
#include <linux/uaccess.h>
#include <linux/syscalls.h>
#include <linux/stat.h>
#include <linux/compat.h>
#include <linux/tracepoint.h>
#include <trace/events/syscalls.h>
#include <asm/syscall.h>
#include <linux/proc_fs.h>
#include <linux/seq_file.h>
#include <linux/kernel.h>
#include <linux/namei.h>
#include <linux/dcache.h>
#include <linux/kdev_t.h>
#include <linux/string.h>
#include <linux/cred.h>
#include <linux/version.h>	/* LINUX_VERSION_CODE: the inode ctime accessor */
#include "susfs_abi.h"
#include "susfs_log.h"
#include "susfs.h"	/* susfs_expose_proc */
#include "ksu_umount_gate.h"	/* susfs_is_current_proc_umounted_app (issue #34) */

/* KSTAT_SPOOF_* bits live in susfs_abi.h (upstream declares them in susfs.h next to struct
 * st_susfs_sus_kstat).  KSTAT_AUTO_SPOOF* below are /proc-interface masks, not supercall ABI. */
#define KSTAT_AUTO_SPOOF (KSTAT_SPOOF_INO | KSTAT_SPOOF_DEV | \
	KSTAT_SPOOF_ATIME_TV_SEC | KSTAT_SPOOF_ATIME_TV_NSEC | \
	KSTAT_SPOOF_MTIME_TV_SEC | KSTAT_SPOOF_MTIME_TV_NSEC | \
	KSTAT_SPOOF_CTIME_TV_SEC | KSTAT_SPOOF_CTIME_TV_NSEC | \
	KSTAT_SPOOF_BLKSIZE | KSTAT_SPOOF_BLOCKS)
#define KSTAT_AUTO_SPOOF_FULL_CLONE (KSTAT_AUTO_SPOOF | \
	KSTAT_SPOOF_NLINK | KSTAT_SPOOF_SIZE)

#define SUS_KSTAT_MAX 32
/* Upstream's target_pathname is char[256]: a shorter buffer truncates a legal long path into a wrong rule. */
#define KSTAT_PATH_MAX 256

struct sus_kstat_entry {
	char target_pathname[KSTAT_PATH_MAX];
	unsigned long target_ino;
	/* dev stored ENCODED (new_encode_dev) so it matches the user statbuf st_dev field 1:1 on the tracepoint hot path. */
	dev_t target_dev;
	unsigned long spoofed_ino;
	unsigned long spoofed_dev;
	unsigned int spoofed_nlink;
	long long spoofed_size;
	long spoofed_atime_tv_sec;
	unsigned long spoofed_atime_tv_nsec;
	long spoofed_mtime_tv_sec;
	unsigned long spoofed_mtime_tv_nsec;
	long spoofed_ctime_tv_sec;
	unsigned long spoofed_ctime_tv_nsec;
	long long spoofed_blocks;
	long spoofed_blksize;
	unsigned int flags;
};

static struct sus_kstat_entry kstat_entries[SUS_KSTAT_MAX];
static int nkstat;
static DEFINE_MUTEX(kstat_lock);

/* Table locking, in two tiers.  kstat_lock (mutex) serialises WRITERS and the /proc read, because
 * writers resolve paths and that sleeps.  kstat_table_lock (spinlock) guards the table for the
 * READERS - the sys_exit tracepoint and the vfs_getattr kretprobe, hot paths where kstat_lock
 * cannot be taken; a reader holds it only long enough to copy the matching entry out and must never
 * copy_to_user under it.  Rule: resolve first (sleeping, outside), then swap (non-sleeping, inside) -
 * publishing a slot before it is filled is a bug (an empty slot used to be visible as soon as nkstat
 * was bumped, before kern_path() had even run). */
static DEFINE_SPINLOCK(kstat_table_lock);

/* The part of an entry a reader needs, copied out under kstat_table_lock. */
struct sus_kstat_snapshot {
	unsigned long spoofed_ino;
	unsigned long spoofed_dev;
	unsigned int spoofed_nlink;
	long long spoofed_size;
	long spoofed_atime_tv_sec;
	unsigned long spoofed_atime_tv_nsec;
	long spoofed_mtime_tv_sec;
	unsigned long spoofed_mtime_tv_nsec;
	long spoofed_ctime_tv_sec;
	unsigned long spoofed_ctime_tv_nsec;
	long long spoofed_blocks;
	long spoofed_blksize;
	unsigned int flags;
};

static void kstat_snapshot(const struct sus_kstat_entry *e,
			   struct sus_kstat_snapshot *s)
{
	s->spoofed_ino = e->spoofed_ino;
	s->spoofed_dev = e->spoofed_dev;
	s->spoofed_nlink = e->spoofed_nlink;
	s->spoofed_size = e->spoofed_size;
	s->spoofed_atime_tv_sec = e->spoofed_atime_tv_sec;
	s->spoofed_atime_tv_nsec = e->spoofed_atime_tv_nsec;
	s->spoofed_mtime_tv_sec = e->spoofed_mtime_tv_sec;
	s->spoofed_mtime_tv_nsec = e->spoofed_mtime_tv_nsec;
	s->spoofed_ctime_tv_sec = e->spoofed_ctime_tv_sec;
	s->spoofed_ctime_tv_nsec = e->spoofed_ctime_tv_nsec;
	s->spoofed_blocks = e->spoofed_blocks;
	s->spoofed_blksize = e->spoofed_blksize;
	s->flags = e->flags;
}

/* arm64 asm-generic struct stat offsets (native 64-bit) */
#define ST_DEV_OFF          0
#define ST_INO_OFF          8
#define ST_NLINK_OFF        20
#define ST_SIZE_OFF         48
#define ST_BLKSIZE_OFF      56
#define ST_BLOCKS_OFF       64
#define ST_ATIME_OFF        72
#define ST_ATIME_NSEC_OFF   80
#define ST_MTIME_OFF        88
#define ST_MTIME_NSEC_OFF   96
#define ST_CTIME_OFF        104
#define ST_CTIME_NSEC_OFF   112

/* The numbers above are a uapi contract, checked at build time instead of trusted: arm64 uses the
 * generic layout (__ARCH_WANT_NEW_STAT), and a DDK header change that moved a member would
 * otherwise corrupt the caller's stat buffer instead of failing this build. */
static_assert(offsetof(struct stat, st_dev) == ST_DEV_OFF, "stat.st_dev");
static_assert(offsetof(struct stat, st_ino) == ST_INO_OFF, "stat.st_ino");
static_assert(offsetof(struct stat, st_nlink) == ST_NLINK_OFF, "stat.st_nlink");
static_assert(offsetof(struct stat, st_size) == ST_SIZE_OFF, "stat.st_size");
static_assert(offsetof(struct stat, st_blksize) == ST_BLKSIZE_OFF, "stat.st_blksize");
static_assert(offsetof(struct stat, st_blocks) == ST_BLOCKS_OFF, "stat.st_blocks");
static_assert(offsetof(struct stat, st_atime) == ST_ATIME_OFF, "stat.st_atime");
static_assert(offsetof(struct stat, st_mtime) == ST_MTIME_OFF, "stat.st_mtime");
static_assert(offsetof(struct stat, st_ctime) == ST_CTIME_OFF, "stat.st_ctime");

/* ---- the read gate ----
 *
 * Upstream gates every sus_kstat read on susfs_is_current_proc_umounted_app(), exactly
 * (TIF_PROC_UMOUNTED && current_uid().val >= 10000).  KernelSU's setuid_hook sets that flag only
 * with the SUSFS integration compiled into the kernel, which this kernel has none of, so the flag
 * is asked of KernelSU itself instead: susfs_is_current_proc_umounted_app() answers it with
 * ksu_uid_should_umount() (ksu_umount_gate.h, issue #34).  The old `uid >= 10000` proxy spoofed for
 * every app uid, the manager and su-granted apps included.
 * Without any gate the spoofing would be visible to root too, wider than upstream.  Writers
 * (supercall, /proc) are configuration and stay ungated. */
static bool susfs_kstat_gate_ok(void)
{
	return susfs_is_current_proc_umounted_app();
}

/* ---- table access ----
 * The *_table_* helpers are the ONLY places that modify kstat_entries or nkstat, each under
 * kstat_table_lock; their callers hold kstat_lock, making the index they pass stable. */

/* Cheapest possible gate for the READ paths: with nothing registered no lookup can match, which on
 * the sys_exit tracepoint saves the two copy_from_user() reads the spoofers do before matching, and
 * on the show_map_vma kprobe (still armed after a `clear`) and the vfs_getattr kretprobe saves an
 * uncontended spinlock per VMA / per lookup.  READ_ONCE is enough: nkstat is published only AFTER
 * the entry it counts has been written, under kstat_table_lock (kstat_table_append stores the entry,
 * then bumps the count), so a stale non-zero value only means work we used to do and a stale zero can
 * cost at most the single read racing the very first add; the authoritative test is the locked lookup.
 * sus_path uses the same idiom (READ_ONCE(sus_path_count)). */
static bool susfs_kstat_table_empty(void)
{
	return READ_ONCE(nkstat) == 0;
}

/* Hot-path lookup: match (ino, dev) and copy the entry out atomically w.r.t. the writers. */
static bool susfs_kstat_lookup(unsigned long ino, dev_t dev,
			       struct sus_kstat_snapshot *out)
{
	unsigned long flags;
	bool found = false;
	int i;

	spin_lock_irqsave(&kstat_table_lock, flags);
	for (i = 0; i < nkstat; i++) {
		if (kstat_entries[i].target_ino == ino &&
		    kstat_entries[i].target_dev == dev) {
			kstat_snapshot(&kstat_entries[i], out);
			found = true;
			break;
		}
	}
	spin_unlock_irqrestore(&kstat_table_lock, flags);
	return found;
}

/* Writer-side lookup by path: safe without the spinlock, since every caller holds kstat_lock. */
static struct sus_kstat_entry *susfs_kstat_find_by_path(const char *path)
{
	int i;

	for (i = 0; i < nkstat; i++)
		if (!strcmp(kstat_entries[i].target_pathname, path))
			return &kstat_entries[i];
	return NULL;
}

/* Append a fully-prepared entry; -ENOSPC when the table is full. */
static int kstat_table_append(const struct sus_kstat_entry *src)
{
	unsigned long flags;
	int idx = -1;

	spin_lock_irqsave(&kstat_table_lock, flags);
	if (nkstat < SUS_KSTAT_MAX) {
		idx = nkstat;
		kstat_entries[idx] = *src;
		nkstat = idx + 1;
	}
	spin_unlock_irqrestore(&kstat_table_lock, flags);
	return idx;
}

/* Replace a live entry wholesale: the reader sees old or new, never a mix of the two. */
static void kstat_table_put(int idx, const struct sus_kstat_entry *src)
{
	unsigned long flags;

	spin_lock_irqsave(&kstat_table_lock, flags);
	if (idx >= 0 && idx < nkstat)
		kstat_entries[idx] = *src;
	spin_unlock_irqrestore(&kstat_table_lock, flags);
}

/* Re-target an entry, and optionally raise its flags. */
static void kstat_table_retarget(int idx, unsigned long ino, dev_t dev,
				 unsigned int add_flags)
{
	unsigned long flags;

	spin_lock_irqsave(&kstat_table_lock, flags);
	if (idx >= 0 && idx < nkstat) {
		kstat_entries[idx].target_ino = ino;
		kstat_entries[idx].target_dev = dev;
		kstat_entries[idx].flags |= add_flags;
	}
	spin_unlock_irqrestore(&kstat_table_lock, flags);
}

/* Remove by index: move the last entry into the hole, under the lock so a reader never sees that move half-done. */
static void kstat_table_del(int idx)
{
	unsigned long flags;

	spin_lock_irqsave(&kstat_table_lock, flags);
	if (idx >= 0 && idx < nkstat) {
		nkstat--;
		if (idx != nkstat)
			kstat_entries[idx] = kstat_entries[nkstat];
	}
	spin_unlock_irqrestore(&kstat_table_lock, flags);
}

static void kstat_table_clear(void)
{
	unsigned long flags;

	spin_lock_irqsave(&kstat_table_lock, flags);
	nkstat = 0;
	spin_unlock_irqrestore(&kstat_table_lock, flags);
}

/* ---- /proc/<pid>/maps coverage ----
 *
 * Upstream's susfs_sus_kstat_spoof_show_map_vma() rewrites dev/ino inside show_map_vma(), where
 * both are still locals, i.e. unreachable from an LKM - and re-printing the line would mean
 * reproducing the kernel's column padding (seq_setwidth()/seq_pad() are not exported, m->pad_until
 * is private state), while a line padded differently from its neighbours is itself a tell.  So the
 * already-formatted line is edited at the return of the function that printed it: the "maj:min ino"
 * run is located by rendering the REAL values the way fs/proc/task_mmu.c does (seq_put_hex_ll for
 * major/minor - lowercase, minimum width 2 - and seq_put_decimal_ull for the ino) and replaced by
 * the spoofed ones.  An earlier version DROPPED the whole line: that closed the stat-vs-maps
 * contradiction but changed the line count (a mapping listed for every process except this one is
 * its own signal) and left smaps unfiltered anyway, its header coming from another call site.
 *
 * The spoofed dev is stored as userspace sees st_dev (new_encode_dev), so it is decoded with
 * new_decode_dev(), the kernel's own inverse, before being printed in the maj:min column; upstream
 * substitutes target_dev into the RAW dev local instead, printing "0:fe4b" for a file whose stat()
 * says 254:75.  Armed on the first rule that spoofs ino or dev. */

/* Same buffer edit as the maps name/numbers rewrite in susfs_open_redirect.c: replace the first
 * occurrence of old[] with new[], growing only when the buffer has room. */
static bool kstat_buf_replace(struct seq_file *m, const char *old, size_t old_len,
			      const char *new, size_t new_len)
{
	char *buf = m->buf;
	size_t count = m->count, i, pos = 0;

	if (!old_len || !new_len || old_len > count)
		return false;
	for (i = 0; i + old_len <= count; i++) {
		if (!memcmp(buf + i, old, old_len)) {
			pos = i;
			break;
		}
	}
	if (i + old_len > count)
		return false;
	if (new_len > old_len && count + (new_len - old_len) >= m->size)
		return false;
	if (new_len != old_len)
		memmove(buf + pos + new_len, buf + pos + old_len, count - (pos + old_len));
	memcpy(buf + pos, new, new_len);
	m->count = count - old_len + new_len;
	return true;
}

struct kstat_map_args {
	struct seq_file *m;
	struct vm_area_struct *vma;
};

static atomic_t n_kstat_map_hits = ATOMIC_INIT(0);
static atomic_t n_kstat_map_rewrites = ATOMIC_INIT(0);

static int kstat_map_vma_entry(struct kretprobe_instance *ri, struct pt_regs *regs)
{
	struct kstat_map_args *a = (struct kstat_map_args *)ri->data;

	a->m = (struct seq_file *)regs->regs[0];
	a->vma = (struct vm_area_struct *)regs->regs[1];
	return 0;
}

static int kstat_map_vma_ret(struct kretprobe_instance *ri, struct pt_regs *regs)
{
	const struct kstat_map_args *a = (const struct kstat_map_args *)ri->data;
	struct seq_file *m = a->m;
	struct vm_area_struct *vma = a->vma;
	struct sus_kstat_snapshot snap;
	struct inode *inode;
	char old[48], new[48];
	unsigned int major, minor;
	int old_len, new_len;

	if (susfs_kstat_table_empty())
		return 0;
	if (!susfs_ptr_plausible(m) || !susfs_ptr_plausible(vma) ||
	    !m->buf || !m->count || !vma->vm_file)
		return 0;
	inode = file_inode(vma->vm_file);
	if (!inode)
		return 0;
	if (!susfs_kstat_gate_ok())
		return 0;
	if (!susfs_kstat_lookup(inode->i_ino,
				new_encode_dev(inode->i_sb->s_dev), &snap))
		return 0;
	if (!(snap.flags & (KSTAT_SPOOF_INO | KSTAT_SPOOF_DEV)))
		return 0;

	atomic_inc(&n_kstat_map_hits);

	/* What the kernel just printed is MAJOR()/MINOR() of the RAW s_dev. */
	old_len = scnprintf(old, sizeof(old), "%02x:%02x %lu",
			    (unsigned int)MAJOR(inode->i_sb->s_dev),
			    (unsigned int)MINOR(inode->i_sb->s_dev),
			    (unsigned long)inode->i_ino);

	if (snap.flags & KSTAT_SPOOF_DEV) {
		unsigned int enc = (unsigned int)snap.spoofed_dev;

		/* new_decode_dev(): the inverse of what cp_new_stat() encoded, so a file whose stat() says 254:75 prints "fe:4b" here too. */
		major = (enc & 0xfff00u) >> 8;
		minor = (enc & 0xffu) | ((enc >> 12) & 0xfff00u);
	} else {
		major = (unsigned int)MAJOR(inode->i_sb->s_dev);
		minor = (unsigned int)MINOR(inode->i_sb->s_dev);
	}
	new_len = scnprintf(new, sizeof(new), "%02x:%02x %lu", major, minor,
			    (snap.flags & KSTAT_SPOOF_INO)
				    ? snap.spoofed_ino
				    : (unsigned long)inode->i_ino);

	/* Keep the column width, space-padding the run: a SHORTER run would pull the name left by the
	 * difference and a line whose name does not line up with its neighbours is visible on its own.
	 * A LONGER run does shift it - the rare case (a spoofed ino with more digits than the real one). */
	while (new_len < old_len && new_len < (int)sizeof(new) - 1)
		new[new_len++] = ' ';

	if (old_len > 0 && new_len > 0 &&
	    kstat_buf_replace(m, old, (size_t)old_len, new, (size_t)new_len))
		atomic_inc(&n_kstat_map_rewrites);
	return 0;
}

static struct kretprobe krp_kstat_map_vma = {
	.kp.symbol_name = "show_map_vma",
	.entry_handler = kstat_map_vma_entry,
	.handler = kstat_map_vma_ret,
	.data_size = sizeof(struct kstat_map_args),
	.maxactive = 16,
};

static bool kstat_maps_registered;

/* Registering sleeps, so this runs from the rule-management paths (kstat_lock held, process context). */
static void kstat_maps_arm(void)
{
	int rc;

	if (kstat_maps_registered)
		return;
	rc = register_kretprobe(&krp_kstat_map_vma);
	if (rc)
		pr_warn("susfs_kstat: register_kretprobe(show_map_vma) failed %d - maps keeps printing the real dev:ino\n",
			rc);
	else {
		kstat_maps_registered = true;
		SUSFS_LOGI("susfs_kstat: maps hook armed (kretprobe show_map_vma)\n");
	}
}

static void kstat_maps_disarm(void)
{
	if (!kstat_maps_registered)
		return;
	unregister_kretprobe(&krp_kstat_map_vma);
	kstat_maps_registered = false;
}

/* rewrite the requested fields of the native user statbuf */
static void susfs_kstat_spoof_statbuf(unsigned long statbuf)
{
	/* Snapshot, not a pointer into the table: a concurrent writer must not be able to retarget the
	 * entry between the match and the copy_to_user below, which must not run under a spinlock. */
	struct sus_kstat_snapshot snap;
	const struct sus_kstat_snapshot *e = &snap;
	unsigned long ino = 0, dev = 0;
	unsigned long v;
	unsigned int v32;
	long long v64;
	long sl;

	if (susfs_kstat_table_empty())
		return;
	if (!susfs_kstat_gate_ok())
		return;

	if (copy_from_user(&ino, (void __user *)(statbuf + ST_INO_OFF), sizeof(ino)))
		return;
	if (copy_from_user(&dev, (void __user *)(statbuf + ST_DEV_OFF), sizeof(dev)))
		return;

	if (!susfs_kstat_lookup(ino, dev, &snap))
		return;

	if (e->flags & KSTAT_SPOOF_INO) {
		v = e->spoofed_ino;
		if (copy_to_user((void __user *)(statbuf + ST_INO_OFF), &v, sizeof(v)))
			return;
	}
	if (e->flags & KSTAT_SPOOF_DEV) {
		v = e->spoofed_dev;
		if (copy_to_user((void __user *)(statbuf + ST_DEV_OFF), &v, sizeof(v)))
			return;
	}
	if (e->flags & KSTAT_SPOOF_NLINK) {
		v32 = e->spoofed_nlink;
		if (copy_to_user((void __user *)(statbuf + ST_NLINK_OFF), &v32, sizeof(v32)))
			return;
	}
	if (e->flags & KSTAT_SPOOF_SIZE) {
		v64 = e->spoofed_size;
		if (copy_to_user((void __user *)(statbuf + ST_SIZE_OFF), &v64, sizeof(v64)))
			return;
	}
	if (e->flags & KSTAT_SPOOF_BLKSIZE) {
		v32 = (unsigned int)e->spoofed_blksize;
		if (copy_to_user((void __user *)(statbuf + ST_BLKSIZE_OFF), &v32, sizeof(v32)))
			return;
	}
	if (e->flags & KSTAT_SPOOF_BLOCKS) {
		v64 = e->spoofed_blocks;
		if (copy_to_user((void __user *)(statbuf + ST_BLOCKS_OFF), &v64, sizeof(v64)))
			return;
	}
	if (e->flags & KSTAT_SPOOF_ATIME_TV_SEC) {
		sl = e->spoofed_atime_tv_sec;
		if (copy_to_user((void __user *)(statbuf + ST_ATIME_OFF), &sl, sizeof(sl)))
			return;
	}
	if (e->flags & KSTAT_SPOOF_ATIME_TV_NSEC) {
		v = e->spoofed_atime_tv_nsec;
		if (copy_to_user((void __user *)(statbuf + ST_ATIME_NSEC_OFF), &v, sizeof(v)))
			return;
	}
	if (e->flags & KSTAT_SPOOF_MTIME_TV_SEC) {
		sl = e->spoofed_mtime_tv_sec;
		if (copy_to_user((void __user *)(statbuf + ST_MTIME_OFF), &sl, sizeof(sl)))
			return;
	}
	if (e->flags & KSTAT_SPOOF_MTIME_TV_NSEC) {
		v = e->spoofed_mtime_tv_nsec;
		if (copy_to_user((void __user *)(statbuf + ST_MTIME_NSEC_OFF), &v, sizeof(v)))
			return;
	}
	if (e->flags & KSTAT_SPOOF_CTIME_TV_SEC) {
		sl = e->spoofed_ctime_tv_sec;
		if (copy_to_user((void __user *)(statbuf + ST_CTIME_OFF), &sl, sizeof(sl)))
			return;
	}
	if (e->flags & KSTAT_SPOOF_CTIME_TV_NSEC) {
		v = e->spoofed_ctime_tv_nsec;
		if (copy_to_user((void __user *)(statbuf + ST_CTIME_NSEC_OFF), &v, sizeof(v)))
			return;
	}
}

/* AArch32 (compat) statbuf layouts.  There are TWO, and which one a syscall fills is decided by
 * its NUMBER, not by the caller being 32-bit:
 *   __NR_stat64 195, __NR_lstat64 196, __NR_fstat64 197, __NR_fstatat64 327 -> struct stat64
 *       (arch/arm64/include/asm/stat.h), filled by cp_new_stat64() via SYSCALL_DEFINE2(stat64)/
 *       (lstat64)/(fstat64) and SYSCALL_DEFINE4(fstatat64) (fs/stat.c, __ARCH_WANT_COMPAT_STAT64);
 *       this struct is NOT struct compat_stat.  All four are handled below (the first three keep
 *       statbuf in args[1], fstatat64 in args[2]).
 *   __NR_stat 106, __NR_lstat 107, __NR_fstat 108 -> struct compat_stat
 *       (arch/arm64/include/asm/compat.h) via cp_compat_stat().  They ARE mapped in this tree's
 *       arch/arm64/include/asm/unistd32.h (106 -> compat_sys_newstat, 107 -> newlstat, 108 ->
 *       newfstat), and an earlier note here claimed the opposite, so a 32-bit caller using
 *       stat()/lstat()/fstat() gets the real numbers while its stat64()/fstat64() are spoofed - a
 *       one-call oracle.  Wiring them needs their own struct compat_stat offsets (st_dev+0, st_ino+4,
 *       st_nlink+10, st_size+20, st_blksize+24, st_blocks+28, atime+32/36, mtime+40/44, ctime+48/52),
 *       which is not a copy of the table below, so it stays a separate change rather than half-done
 *       here.  They are listed so nobody concludes "compat = compat_stat" and wires the wrong
 *       offsets - which is what this code used to do: st_ino was read at +4, the HIGH half of st_dev
 *       in stat64 and always 0, so the lookup could never match (a match would have written into
 *       st_dev/st_rdev).
 *
 * ALIGNMENT (these numbers were established twice): compat_u64/compat_s64 are
 * __attribute__((aligned(4))) only when CONFIG_COMPAT_FOR_U64_ALIGNMENT is set
 * (include/asm-generic/compat.h), and only the 32-bit arm architecture selects it - so on this
 * arm64 kernel the plain `typedef s64 compat_s64;` applies, u64 members keep natural 8-byte
 * alignment, and st_size is at +48 (not +44), st_ino at +96 (not +88).  A 4-byte-aligned read is
 * not a silent near-miss - measured on device with tools/susfs_compat_stat, a 6-byte file reported
 * size=25769803776 = 6 << 32 (low half from padding, high half from the value).  The offsets below
 * are what that client and the kernel agree on. */
#define STAT64_ST_DEV_OFF       0	/* compat_u64 */
#define STAT64_ST_BROKEN_INO_OFF 12	/* compat_ulong_t __st_ino (one of the two ino fields) */
#define STAT64_ST_NLINK_OFF     20	/* compat_uint_t */
#define STAT64_ST_SIZE_OFF      48	/* compat_s64 */
#define STAT64_ST_BLKSIZE_OFF   56	/* compat_ulong_t */
#define STAT64_ST_BLOCKS_OFF    64	/* compat_u64 */
#define STAT64_ST_ATIME_OFF     72
#define STAT64_ST_ATIME_NSEC_OFF 76
#define STAT64_ST_MTIME_OFF     80
#define STAT64_ST_MTIME_NSEC_OFF 84
#define STAT64_ST_CTIME_OFF     88
#define STAT64_ST_CTIME_NSEC_OFF 92
#define STAT64_ST_INO_OFF       96	/* compat_u64 st_ino (also written; the KEY is read from +12) */
#define STAT64_ST_SIZE          104

/* ARM EABI syscall numbers that fill struct stat64 (arch/arm64/include/asm/unistd32.h; the
 * statbuf argument position is from fs/stat.c's COMPAT_SYSCALL_DEFINE2/4). */
#define COMPAT_FSTATAT64_NR	327	/* fstatat64(dfd, path, statbuf, flag) */
#define COMPAT_STAT64_NR	195	/* stat64(path, statbuf) */
#define COMPAT_LSTAT64_NR	196	/* lstat64(path, statbuf) */
#define COMPAT_FSTAT64_NR	197	/* fstat64(fd, statbuf) */

/* compat (32-bit) statbuf: struct stat64 (see above) - the layout all four handled syscalls use. */
static void susfs_kstat_spoof_compat_statbuf(unsigned long statbuf)
{
	struct sus_kstat_snapshot snap;
	const struct sus_kstat_snapshot *e = &snap;
	unsigned long long v64;
	unsigned int ino = 0, dev = 0;
	unsigned int v32;
	int v;

	if (susfs_kstat_table_empty())
		return;
	if (!susfs_kstat_gate_ok())
		return;

	/* Key lookup on what the kernel ACTUALLY filled: __st_ino at +12.  stat64 carries the
	 * STAT64_HAS_BROKEN_ST_INO marker (arch/arm64/include/asm/stat.h), so cp_new_stat64() writes
	 * __st_ino and leaves st_ino (+96) alone - reading the key from +96 would compare against
	 * whatever the caller's buffer held and never match.  Both fields are written when spoofing, so
	 * a libc that synthesises st_ino from __st_ino and one that reads st_ino directly both see the
	 * spoofed value. */
	if (copy_from_user(&ino, (void __user *)(statbuf + STAT64_ST_BROKEN_INO_OFF), sizeof(ino)))
		return;
	if (copy_from_user(&dev, (void __user *)(statbuf + STAT64_ST_DEV_OFF), sizeof(dev)))
		return;
	if (!susfs_kstat_lookup(ino, dev, &snap))
		return;

	if (e->flags & KSTAT_SPOOF_INO) {
		v32 = (unsigned int)e->spoofed_ino;
		if (copy_to_user((void __user *)(statbuf + STAT64_ST_BROKEN_INO_OFF), &v32, sizeof(v32)))
			return;
		v64 = (unsigned long long)e->spoofed_ino;
		if (copy_to_user((void __user *)(statbuf + STAT64_ST_INO_OFF), &v64, sizeof(v64)))
			return;
	}
	if (e->flags & KSTAT_SPOOF_DEV) {
		v64 = (unsigned long long)e->spoofed_dev;
		if (copy_to_user((void __user *)(statbuf + STAT64_ST_DEV_OFF), &v64, sizeof(v64)))
			return;
	}
	if (e->flags & KSTAT_SPOOF_NLINK) {
		v32 = (unsigned int)e->spoofed_nlink;
		if (copy_to_user((void __user *)(statbuf + STAT64_ST_NLINK_OFF), &v32, sizeof(v32)))
			return;
	}
	if (e->flags & KSTAT_SPOOF_SIZE) {
		v64 = (unsigned long long)e->spoofed_size;
		if (copy_to_user((void __user *)(statbuf + STAT64_ST_SIZE_OFF), &v64, sizeof(v64)))
			return;
	}
	if (e->flags & KSTAT_SPOOF_BLKSIZE) {
		v32 = (unsigned int)e->spoofed_blksize;
		if (copy_to_user((void __user *)(statbuf + STAT64_ST_BLKSIZE_OFF), &v32, sizeof(v32)))
			return;
	}
	if (e->flags & KSTAT_SPOOF_BLOCKS) {
		v64 = (unsigned long long)e->spoofed_blocks;
		if (copy_to_user((void __user *)(statbuf + STAT64_ST_BLOCKS_OFF), &v64, sizeof(v64)))
			return;
	}
	if (e->flags & KSTAT_SPOOF_ATIME_TV_SEC) {
		v = (int)e->spoofed_atime_tv_sec;
		if (copy_to_user((void __user *)(statbuf + STAT64_ST_ATIME_OFF), &v, sizeof(v)))
			return;
	}
	if (e->flags & KSTAT_SPOOF_ATIME_TV_NSEC) {
		v32 = (unsigned int)e->spoofed_atime_tv_nsec;
		if (copy_to_user((void __user *)(statbuf + STAT64_ST_ATIME_NSEC_OFF), &v32, sizeof(v32)))
			return;
	}
	if (e->flags & KSTAT_SPOOF_MTIME_TV_SEC) {
		v = (int)e->spoofed_mtime_tv_sec;
		if (copy_to_user((void __user *)(statbuf + STAT64_ST_MTIME_OFF), &v, sizeof(v)))
			return;
	}
	if (e->flags & KSTAT_SPOOF_MTIME_TV_NSEC) {
		v32 = (unsigned int)e->spoofed_mtime_tv_nsec;
		if (copy_to_user((void __user *)(statbuf + STAT64_ST_MTIME_NSEC_OFF), &v32, sizeof(v32)))
			return;
	}
	if (e->flags & KSTAT_SPOOF_CTIME_TV_SEC) {
		v = (int)e->spoofed_ctime_tv_sec;
		if (copy_to_user((void __user *)(statbuf + STAT64_ST_CTIME_OFF), &v, sizeof(v)))
			return;
	}
	if (e->flags & KSTAT_SPOOF_CTIME_TV_NSEC) {
		v32 = (unsigned int)e->spoofed_ctime_tv_nsec;
		if (copy_to_user((void __user *)(statbuf + STAT64_ST_CTIME_NSEC_OFF), &v32, sizeof(v32)))
			return;
	}
}

/* sys_exit tracepoint: the user statbuf is fully written by now, and syscall_get_arguments()
 * still returns the original args (verified: args[2] == statbuf), so no per-cpu state is needed.
 *
 * It carries two features: the stat family below, and sus_path's directory-listing rewrite.  The
 * listing side needs its own gate - see the note above sus_path_dirent_layout_id(): a syscall
 * number alone does not identify a call (arm64's native 141 is getpriority where AArch32 numbers
 * getdents 141), so the number is only ever read together with the caller's ABI.
 *
 * COST: this callback runs for every syscall exit, so the three checks below (is_compat_task(),
 * syscall_get_nr(), the classifier) are paid on all of them - a function call and a couple of
 * compares.  The callback itself was measured when the stat family moved onto it at ~28 ns per
 * syscall (getpid 113 -> 141 ns); that number is the baseline this adds to, and it has not been
 * re-measured for the listing filter (no device was available for this change).
 *
 * KNOWN BOUNDARY (ptrace): arch/arm64/kernel/syscall.c writes regs->syscallno = scno BEFORE
 * syscall_trace_enter(), so a tracer that rewrites a getdents64 into another syscall still gets
 * classified here as getdents64; the parse then fails on a buffer that is not a dirent chain and
 * counts a rewrite failure.  It cannot corrupt anything (every read is bounded by d_reclen and
 * every failure answers "nothing filtered"), and the stat family below has the same exposure. */
static void kstat_sys_exit(void *data, struct pt_regs *regs, long ret)
{
	unsigned long args[6];
	bool compat = is_compat_task();
	long nr = syscall_get_nr(current, regs);
	int lay = sus_path_dirent_layout_id(nr, compat);

	if (lay >= 0) {
		long rc;

		/* Nothing to rewrite when the syscall produced no bytes (an error, or the end of
		 * the directory), and the arguments must not be read before the gate said this
		 * really is a listing call.  The same goes for the armed flag: with no rules yet
		 * (or with no_extra) there is nothing to do, and that is the common case. */
		if (ret <= 0 || !sus_path_dirent_armed())
			return;
		syscall_get_arguments(current, regs, args);
		rc = sus_path_dirent_filter(lay,
					    compat ? (unsigned long)compat_ptr((u32)args[1])
						   : args[1],
					    ret);
		if (rc != ret)
			syscall_set_return_value(current, regs, 0, rc);
		return;
	}

	if (ret != 0)
		return;
	syscall_get_arguments(current, regs, args);

	/* The statbuf argument is NOT the same one for every syscall, so the NULL check has to live
	 * inside each branch: fstat64(fd, statbuf) keeps it in args[1], and checking args[2] first
	 * made every 32-bit fstat64() return early - the rule applied to fstatat64, not to fstat64. */
	if (compat) {
		switch (nr) {
		case COMPAT_FSTATAT64_NR:
			susfs_kstat_spoof_compat_statbuf((unsigned long)compat_ptr((u32)args[2]));
			break;
		/* stat64/lstat64/fstat64: all three keep statbuf in args[1], and all three fill the
		 * same struct stat64 this helper expects. */
		case COMPAT_STAT64_NR:
		case COMPAT_LSTAT64_NR:
		case COMPAT_FSTAT64_NR:
			susfs_kstat_spoof_compat_statbuf((unsigned long)compat_ptr((u32)args[1]));
			break;
		}
	} else {
		if (nr != __NR_newfstatat)
			return;
		if (!args[2])
			return;
		susfs_kstat_spoof_statbuf(args[2]);
	}
}

/* fallback: some paths (vfs_fstat, statx, direct callers) still reach the exported vfs_getattr
 * copy; rewrite the kernel kstat there too. */
struct vfs_getattr_args {
	const struct path *path;
	struct kstat *stat;
};

static int kr_vfs_getattr_entry(struct kretprobe_instance *ri, struct pt_regs *regs)
{
	struct vfs_getattr_args *a = (struct vfs_getattr_args *)ri->data;

	a->path = (const struct path *)regs->regs[0];
	a->stat = (struct kstat *)regs->regs[1];
	return 0;
}

static void susfs_kstat_spoof_kstat(struct inode *inode, struct kstat *stat)
{
	struct sus_kstat_snapshot snap;
	const struct sus_kstat_snapshot *e = &snap;

	if (susfs_kstat_table_empty())
		return;
	if (!inode || !stat)
		return;
	if (!susfs_kstat_gate_ok())
		return;
	if (!susfs_kstat_lookup(inode->i_ino, new_encode_dev(inode->i_sb->s_dev),
				&snap))
		return;
	if (e->flags & KSTAT_SPOOF_INO)
		stat->ino = e->spoofed_ino;
	if (e->flags & KSTAT_SPOOF_DEV)
		stat->dev = new_decode_dev(e->spoofed_dev);
	if (e->flags & KSTAT_SPOOF_NLINK)
		stat->nlink = e->spoofed_nlink;
	if (e->flags & KSTAT_SPOOF_SIZE)
		stat->size = e->spoofed_size;
	if (e->flags & KSTAT_SPOOF_BLKSIZE)
		stat->blksize = e->spoofed_blksize;
	if (e->flags & KSTAT_SPOOF_BLOCKS)
		stat->blocks = e->spoofed_blocks;
	if (e->flags & KSTAT_SPOOF_ATIME_TV_SEC)
		stat->atime.tv_sec = e->spoofed_atime_tv_sec;
	if (e->flags & KSTAT_SPOOF_ATIME_TV_NSEC)
		stat->atime.tv_nsec = e->spoofed_atime_tv_nsec;
	if (e->flags & KSTAT_SPOOF_MTIME_TV_SEC)
		stat->mtime.tv_sec = e->spoofed_mtime_tv_sec;
	if (e->flags & KSTAT_SPOOF_MTIME_TV_NSEC)
		stat->mtime.tv_nsec = e->spoofed_mtime_tv_nsec;
	if (e->flags & KSTAT_SPOOF_CTIME_TV_SEC)
		stat->ctime.tv_sec = e->spoofed_ctime_tv_sec;
	if (e->flags & KSTAT_SPOOF_CTIME_TV_NSEC)
		stat->ctime.tv_nsec = e->spoofed_ctime_tv_nsec;
}

/* Counters, because "registered" and "reached" are different claims everywhere in this module:
 * the sys_exit rewrite handles newfstatat, and this fallback covers the paths that never go
 * through that wrapper (fstat(2), statx(2), any caller of the exported vfs_getattr).  If these
 * stay at 0 through a run that calls fstat/statx, the probe is dead weight and has to go - the
 * same test the maps hook, __d_path and pin_user_pages_remote failed. */
static atomic_t n_gattr_hits = ATOMIC_INIT(0);
static atomic_t n_gattr_spoofs = ATOMIC_INIT(0);

static int kr_vfs_getattr_ret(struct kretprobe_instance *ri, struct pt_regs *regs)
{
	struct vfs_getattr_args *a = (struct vfs_getattr_args *)ri->data;
	struct inode *inode;
	struct sus_kstat_snapshot snap;

	if (regs_return_value(regs) != 0)
		return 0;
	if (!a->path || !a->path->dentry || !a->stat)
		return 0;
	inode = a->path->dentry->d_inode;

	atomic_inc(&n_gattr_hits);
	if (inode && susfs_kstat_gate_ok() &&
	    susfs_kstat_lookup(inode->i_ino, new_encode_dev(inode->i_sb->s_dev),
			       &snap))
		atomic_inc(&n_gattr_spoofs);

	susfs_kstat_spoof_kstat(inode, a->stat);
	return 0;
}

static struct kretprobe krp_vfs_getattr = {
	.kp.symbol_name = "vfs_getattr",
	.entry_handler = kr_vfs_getattr_entry,
	.handler = kr_vfs_getattr_ret,
	.data_size = sizeof(struct vfs_getattr_args),
	.maxactive = 64,
};

/* ---- path resolution + rule management (original SUSFS semantics) ---- */

/* resolve <path> to its CURRENT (ino, encoded dev).  Sleeps - never call it with kstat_table_lock held. */
static int susfs_kstat_resolve(const char *path, unsigned long *ino, dev_t *dev)
{
	struct path p;
	struct inode *inode;
	int err;

	err = kern_path(path, 0, &p);
	if (err)
		return err;
	inode = d_backing_inode(p.dentry);
	if (!inode) {
		path_put(&p);
		return -ENOENT;
	}
	*ino = inode->i_ino;
	*dev = new_encode_dev(inode->i_sb->s_dev);
	path_put(&p);
	return 0;
}

/* resolve <path> and fill the spoofed_* fields with its CURRENT stat (the generic_fillattr
 * mapping).  Fills a DETACHED entry only: callers build here, then commit through one of the
 * kstat_table_* helpers, so nothing half-built is ever visible to a reader. */
static int susfs_kstat_fill_from_path(struct sus_kstat_entry *e, const char *path)
{
	struct path p;
	struct inode *inode;
	int err;
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 6, 0)
	/* 6.6 renamed the inode field to __i_ctime and marked it private ("use inode_*_ctime
	 * accessors!"), so reading it stopped compiling: "no member named 'i_ctime' in 'struct inode'".
	 * inode_get_ctime() returns the very same struct timespec64 by value, and this gate is
	 * release-aligned as well as upstream-aligned: v6.6 added the accessor upstream and is also the
	 * GKI tree boundary.  i_atime/i_mtime were NOT renamed here - upstream split them into time64_t
	 * i_atime_sec/i_mtime_sec plus u32 i_atime_nsec/i_mtime_nsec, read through inode_get_atime()/
	 * inode_get_mtime(), in v6.11, which is not a release this module builds for - so those two keep
	 * being read directly. */
	struct timespec64 ctime;
#endif

	err = kern_path(path, 0, &p);
	if (err)
		return err;
	inode = d_backing_inode(p.dentry);
	if (!inode) {
		path_put(&p);
		return -ENOENT;
	}

#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 6, 0)
	ctime = inode_get_ctime(inode);
#endif

	e->target_ino = inode->i_ino;
	e->target_dev = new_encode_dev(inode->i_sb->s_dev);
	e->spoofed_ino = inode->i_ino;
	e->spoofed_dev = new_encode_dev(inode->i_sb->s_dev);
	e->spoofed_nlink = inode->i_nlink;
	e->spoofed_size = inode->i_size;
	e->spoofed_atime_tv_sec = inode->i_atime.tv_sec;
	e->spoofed_atime_tv_nsec = inode->i_atime.tv_nsec;
	e->spoofed_mtime_tv_sec = inode->i_mtime.tv_sec;
	e->spoofed_mtime_tv_nsec = inode->i_mtime.tv_nsec;
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 6, 0)
	e->spoofed_ctime_tv_sec = ctime.tv_sec;
	e->spoofed_ctime_tv_nsec = ctime.tv_nsec;
#else
	e->spoofed_ctime_tv_sec = inode->i_ctime.tv_sec;
	e->spoofed_ctime_tv_nsec = inode->i_ctime.tv_nsec;
#endif
	e->spoofed_blocks = inode->i_blocks;
	e->spoofed_blksize = 1 << inode->i_blkbits;

	path_put(&p);
	return 0;
}

/* re-resolve only target_ino/target_dev; spoofed values stay untouched.  Resolve first (sleeping),
 * then re-target under the lock: a reader sees the old pair or the new pair, never ino-of-B with
 * dev-of-A. */
static int susfs_kstat_update(const char *path, bool full_clone)
{
	struct sus_kstat_entry *e;
	unsigned long ino;
	dev_t dev;
	int err;

	e = susfs_kstat_find_by_path(path);
	if (!e)
		return -ENOENT;
	err = susfs_kstat_resolve(path, &ino, &dev);
	if (err)
		return err;
	kstat_table_retarget((int)(e - kstat_entries), ino, dev,
			     full_clone ? KSTAT_AUTO_SPOOF_FULL_CLONE
					: KSTAT_AUTO_SPOOF);
	return 0;
}

/* add/update a rule from its pathname; kstat_lock held */
static int susfs_kstat_add(const char *path)
{
	struct sus_kstat_entry tmp;
	struct sus_kstat_entry *e;
	int err, idx;

	if (strlen(path) >= KSTAT_PATH_MAX)
		return -ENAMETOOLONG;

	e = susfs_kstat_find_by_path(path);

	memset(&tmp, 0, sizeof(tmp));
	err = susfs_kstat_fill_from_path(&tmp, path);
	if (err)
		return err;
	strscpy(tmp.target_pathname, path, KSTAT_PATH_MAX);
	tmp.flags = KSTAT_AUTO_SPOOF;

	if (e) {
		kstat_table_put((int)(e - kstat_entries), &tmp);
		return 0;
	}
	idx = kstat_table_append(&tmp);
	return idx < 0 ? -ENOSPC : 0;
}

static void susfs_kstat_del(const char *path)
{
	struct sus_kstat_entry *e = susfs_kstat_find_by_path(path);

	if (!e)
		return;
	kstat_table_del((int)(e - kstat_entries));
}

/* parse "default" -> *is_default=true, else parse signed 64-bit int */
static int parse_override(const char *tok, bool *is_default, long long *val)
{
	if (!strcmp(tok, "default")) {
		*is_default = true;
		return 0;
	}
	*is_default = false;
	return kstrtoll(tok, 10, val);
}

/* add_sus_kstat_statically: 12 fields follow the path, each a number or "default". */
static int susfs_kstat_add_statically(char **argv, int argc)
{
	struct sus_kstat_entry tmp;
	struct sus_kstat_entry *e;
	long long val;
	bool dflt;
	int err, i, idx;
	/* field index -> flag and setter, ordered as the CLI:
	 * ino dev nlink size atime atime_nsec mtime mtime_nsec
	 * ctime ctime_nsec blocks blksize */
	static const unsigned int f_flags[12] = {
		KSTAT_SPOOF_INO, KSTAT_SPOOF_DEV, KSTAT_SPOOF_NLINK,
		KSTAT_SPOOF_SIZE, KSTAT_SPOOF_ATIME_TV_SEC,
		KSTAT_SPOOF_ATIME_TV_NSEC, KSTAT_SPOOF_MTIME_TV_SEC,
		KSTAT_SPOOF_MTIME_TV_NSEC, KSTAT_SPOOF_CTIME_TV_SEC,
		KSTAT_SPOOF_CTIME_TV_NSEC, KSTAT_SPOOF_BLOCKS,
		KSTAT_SPOOF_BLKSIZE,
	};
	const char *path = argv[1];

	/* argv[2 + i] below reaches argv[13], so this needs argv[14]: assert it here rather than only
	 * at the call site, which checks `argc == 14` against a 16-slot argv - a future caller that
	 * forgot would read past the array. */
	if (argc < 2 + (int)ARRAY_SIZE(f_flags))
		return -EINVAL;

	if (strlen(path) >= KSTAT_PATH_MAX)
		return -ENAMETOOLONG;

	e = susfs_kstat_find_by_path(path);

	memset(&tmp, 0, sizeof(tmp));
	/* start from the CURRENT stat; non-default fields override it */
	err = susfs_kstat_fill_from_path(&tmp, path);
	if (err)
		return err;
	strscpy(tmp.target_pathname, path, KSTAT_PATH_MAX);
	tmp.flags = 0;

	for (i = 0; i < 12; i++) {
		err = parse_override(argv[2 + i], &dflt, &val);
		if (err)
			return err;
		if (dflt)
			continue;
		tmp.flags |= f_flags[i];
		switch (i) {
		case 0: tmp.spoofed_ino = (unsigned long)val; break;
		case 1: tmp.spoofed_dev = (unsigned long)val; break;
		case 2: tmp.spoofed_nlink = (unsigned int)val; break;
		case 3: tmp.spoofed_size = val; break;
		case 4: tmp.spoofed_atime_tv_sec = (long)val; break;
		case 5: tmp.spoofed_atime_tv_nsec = (unsigned long)val; break;
		case 6: tmp.spoofed_mtime_tv_sec = (long)val; break;
		case 7: tmp.spoofed_mtime_tv_nsec = (unsigned long)val; break;
		case 8: tmp.spoofed_ctime_tv_sec = (long)val; break;
		case 9: tmp.spoofed_ctime_tv_nsec = (unsigned long)val; break;
		case 10: tmp.spoofed_blocks = val; break;
		case 11: tmp.spoofed_blksize = (long)val; break;
		}
	}

	if (e) {
		kstat_table_put((int)(e - kstat_entries), &tmp);
		return 0;
	}
	idx = kstat_table_append(&tmp);
	return idx < 0 ? -ENOSPC : 0;
}

/* statically-add from the supercall ABI struct (is_statically=1): copy the caller's 12 spoofed
 * fields + flags verbatim; resolve target ino/dev here. */
static int susfs_kstat_add_statically_abi(struct st_susfs_sus_kstat *info)
{
	struct sus_kstat_entry tmp;
	struct sus_kstat_entry *e;
	int err, idx;

	e = susfs_kstat_find_by_path(info->target_pathname);

	memset(&tmp, 0, sizeof(tmp));
	err = susfs_kstat_fill_from_path(&tmp, info->target_pathname);
	if (err)
		return err;
	strscpy(tmp.target_pathname, info->target_pathname, KSTAT_PATH_MAX);

	tmp.spoofed_ino = info->spoofed_ino;
	tmp.spoofed_dev = info->spoofed_dev;
	tmp.spoofed_nlink = info->spoofed_nlink;
	tmp.spoofed_size = info->spoofed_size;
	tmp.spoofed_atime_tv_sec = info->spoofed_atime_tv_sec;
	tmp.spoofed_atime_tv_nsec = info->spoofed_atime_tv_nsec;
	tmp.spoofed_mtime_tv_sec = info->spoofed_mtime_tv_sec;
	tmp.spoofed_mtime_tv_nsec = info->spoofed_mtime_tv_nsec;
	tmp.spoofed_ctime_tv_sec = info->spoofed_ctime_tv_sec;
	tmp.spoofed_ctime_tv_nsec = info->spoofed_ctime_tv_nsec;
	tmp.spoofed_blocks = info->spoofed_blocks;
	tmp.spoofed_blksize = info->spoofed_blksize;
	tmp.flags = info->flags;

	if (e) {
		kstat_table_put((int)(e - kstat_entries), &tmp);
		return 0;
	}
	idx = kstat_table_append(&tmp);
	return idx < 0 ? -ENOSPC : 0;
}

/* supercall: CMD_SUSFS_ADD_SUS_KSTAT / UPDATE / STATICALLY */
void susfs_kstat_supercall(unsigned int cmd, void __user **arg)
{
	struct st_susfs_sus_kstat info = {0};
	int err = -EINVAL;

	if (copy_from_user(&info, (void __user *)*arg, sizeof(info))) {
		info.err = -EFAULT;
		goto out;
	}

	/* All three commands key on target_pathname, and a caller may fill all 256 bytes of that field -
	 * reject an unterminated one before any strlen() or kern_path() can walk off our stack copy. */
	if (!susfs_abi_path_ok(info.target_pathname, sizeof(info.target_pathname))) {
		info.err = -ENAMETOOLONG;
		goto out;
	}

	mutex_lock(&kstat_lock);
	switch (cmd) {
	case CMD_SUSFS_ADD_SUS_KSTAT:
		err = susfs_kstat_add(info.target_pathname);
		break;
	case CMD_SUSFS_ADD_SUS_KSTAT_STATICALLY:
		err = susfs_kstat_add_statically_abi(&info);
		break;
	case CMD_SUSFS_UPDATE_SUS_KSTAT:
		err = susfs_kstat_update(info.target_pathname, false);
		break;
	}
	mutex_unlock(&kstat_lock);
	info.err = err;
	/* Armed outside the lock and only after a rule actually landed: a hook that can never fire is worse than no hook. */
	if (!err)
		kstat_maps_arm();
out:
	/* Upstream (fs/susfs.c susfs_add_sus_kstat) writes back ONLY the err field for this
	 * input-type command, never the whole struct: copying the full struct back would overrun a
	 * caller whose own struct is smaller/differently laid out (the prebuilt ksu_susfs tool) and
	 * corrupt its stack - match upstream exactly. */
	if (copy_to_user(&((struct st_susfs_sus_kstat __user *)*arg)->err,
			 &info.err, sizeof(info.err)))
		pr_warn("kstat supercall copy_to_user failed\n");
}

/* ---- /proc/susfs_kstat: runtime rule management ---- */
static int kstat_proc_show(struct seq_file *m, void *v);
static int kstat_proc_open(struct inode *inode, struct file *file);
static ssize_t kstat_proc_write(struct file *file, const char __user *buf,
                                size_t len, loff_t *off);

static const struct proc_ops kstat_proc_ops = {
	.proc_open = kstat_proc_open,
	.proc_read = seq_read,
	.proc_write = kstat_proc_write,
	.proc_lseek = seq_lseek,
	.proc_release = single_release,
};

static struct proc_dir_entry *kstat_proc_entry;

static bool kstat_tp_registered;
static bool kstat_krp_registered;

/* sus_path's listing filter rides this tracepoint but does not register it (the stat family
 * here does), so it has to be able to tell whether the ride exists: with the registration
 * failed, the filter would be silently dead while sus_path still reported itself armed. */
bool susfs_kstat_tracepoint_armed(void)
{
	return READ_ONCE(kstat_tp_registered);
}

int susfs_kstat_init(void)
{
	int rc;

	/* The hooks are armed UNCONDITIONALLY, and that is not cosmetic: the supercall interface
	 * (CMD_SUSFS_ADD_SUS_KSTAT) can install rules with no /proc node at all, so skipping
	 * registration when expose_proc=0 silently turned the whole feature into a no-op - rules
	 * accepted, never applied.  expose_proc decides whether the node exists, nothing else. */
	rc = register_trace_sys_exit(kstat_sys_exit, NULL);
	if (rc)
		pr_warn("register_trace_sys_exit failed %d\n", rc);
	else
		kstat_tp_registered = true;

	rc = register_kretprobe(&krp_vfs_getattr);
	if (rc)
		pr_warn("register_kretprobe(vfs_getattr) failed %d\n", rc);
	else
		kstat_krp_registered = true;

	/* 0777 is deliberate, not an oversight.  inode_permission() runs the DAC check BEFORE
	 * security_inode_permission(), so a node the app cannot open hands it EACCES - "this exists,
	 * you may not read it" - instead of the ENOENT sus_path is supposed to produce.  0777 lets DAC
	 * pass and leaves the answer to sus_path's LSM layer, which then becomes the ONLY thing
	 * between an app and a world-writable control node - so without that layer the node is not
	 * created at all, see susfs_control_node_allowed(). */
	if (susfs_control_node_allowed()) {
		kstat_proc_entry = proc_create("susfs_kstat", 0777, NULL,
					       &kstat_proc_ops);
		if (!kstat_proc_entry)
			pr_warn("proc_create(susfs_kstat) failed\n");
	} else {
		SUSFS_LOGI("susfs_kstat: /proc node not created (expose_proc=%d lsm=%d)\n",
			(int)susfs_expose_proc, (int)sus_path_lsm_active());
	}

	SUSFS_LOGI("kstat armed: %d rules (tp=%d krp=%d proc=%d)\n", nkstat,
		kstat_tp_registered, kstat_krp_registered,
		kstat_proc_entry != NULL);
	return 0;
}

void susfs_kstat_exit(void)
{
	kstat_maps_disarm();
	if (kstat_krp_registered) {
		unregister_kretprobe(&krp_vfs_getattr);
		kstat_krp_registered = false;
	}
	if (kstat_tp_registered) {
		unregister_trace_sys_exit(kstat_sys_exit, NULL);
		tracepoint_synchronize_unregister();
		kstat_tp_registered = false;
	}
	if (kstat_proc_entry) {
		proc_remove(kstat_proc_entry);
		kstat_proc_entry = NULL;
	}
	kstat_table_clear();
}

static int kstat_proc_show(struct seq_file *m, void *v)
{
	int i;

	mutex_lock(&kstat_lock);
	if (nkstat == 0) {
		seq_puts(m, "(empty)\n");
	} else {
		for (i = 0; i < nkstat; i++) {
			struct sus_kstat_entry *e = &kstat_entries[i];

			seq_printf(m,
				"%s ino=%lu dev=%lu flags=0x%x"
				" [ino=%lu dev=%lu nlink=%u size=%lld"
				" atime=%ld.%lu mtime=%ld.%lu ctime=%ld.%lu"
				" blocks=%lld blksize=%ld]\n",
				e->target_pathname, e->target_ino,
				(unsigned long)e->target_dev, e->flags,
				e->spoofed_ino, e->spoofed_dev, e->spoofed_nlink,
				e->spoofed_size,
				e->spoofed_atime_tv_sec, e->spoofed_atime_tv_nsec,
				e->spoofed_mtime_tv_sec, e->spoofed_mtime_tv_nsec,
				e->spoofed_ctime_tv_sec, e->spoofed_ctime_tv_nsec,
				e->spoofed_blocks, e->spoofed_blksize);
		}
	}
	mutex_unlock(&kstat_lock);
	/* "armed" is not "fired": the maps hook has to be readable the same way the other feature
	 * hooks are, or a rewrite that never happens looks identical to one that works. */
	seq_printf(m, "maps: armed=%d hits=%d rewrites=%d\n",
		   kstat_maps_registered, atomic_read(&n_kstat_map_hits),
		   atomic_read(&n_kstat_map_rewrites));
	seq_printf(m, "vfs_getattr fallback: gattr_hits=%d gattr_spoofs=%d\n",
		   atomic_read(&n_gattr_hits), atomic_read(&n_gattr_spoofs));
	return 0;
}

static int kstat_proc_open(struct inode *inode, struct file *file)
{
	/* root-only, like kstat_proc_open() above - 0777 is deliberate (see susfs_kstat_init()) */
	if (current_uid().val != 0)
		return -ENOENT;
	return single_open(file, kstat_proc_show, NULL);
}

static int split_ws(char *buf, char **argv, int max)
{
	int argc = 0;
	char *p = buf;

	while (argc < max) {
		while (*p == ' ' || *p == '\t' || *p == '\n')
			p++;
		if (*p == '\0')
			break;
		argv[argc++] = p;
		while (*p && *p != ' ' && *p != '\t' && *p != '\n')
			p++;
		if (*p)
			*p++ = '\0';
	}
	return argc;
}

static ssize_t kstat_proc_write(struct file *file, const char __user *buf,
                                size_t len, loff_t *off)
{
	char cmd[768];
	char *argv[16];
	int argc, err;

	/* Same gate as kstat_proc_open(): open() alone is not enough - an fd opened by root and
	 * handed on would keep working, which is why the sibling files check both. */
	if (current_uid().val != 0)
		return -ENOENT;

	if (len >= sizeof(cmd))
		len = sizeof(cmd) - 1;
	if (copy_from_user(cmd, buf, len))
		return -EFAULT;
	cmd[len] = 0;

	argc = split_ws(cmd, argv, 16);
	if (argc == 0)
		return len;

	mutex_lock(&kstat_lock);
	err = -EINVAL;

	if (!strcmp(argv[0], "add_sus_kstat") && argc == 2)
		err = susfs_kstat_add(argv[1]);
	else if (!strcmp(argv[0], "add_sus_kstat_statically") && argc == 14)
		err = susfs_kstat_add_statically(argv, argc);
	else if (!strcmp(argv[0], "update_sus_kstat") && argc == 2)
		err = susfs_kstat_update(argv[1], false);
	else if (!strcmp(argv[0], "update_sus_kstat_full_clone") && argc == 2)
		err = susfs_kstat_update(argv[1], true);
	else if (!strcmp(argv[0], "del") && argc == 2) {
		susfs_kstat_del(argv[1]);
		err = 0;
	} else if (!strcmp(argv[0], "clear")) {
		kstat_table_clear();
		err = 0;
	}

	mutex_unlock(&kstat_lock);

	if (!err)
		kstat_maps_arm();

	if (err) {
		pr_warn("kstat proc write '%s' -> err %d\n", argv[0], err);
		/* Reported to the writer: a command that did not take effect must not look like a
		 * successful full write.  Success still returns len, so callers that expect a complete
		 * write keep working. */
		return err;
	}
	return len;
}
