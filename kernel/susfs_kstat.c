// SPDX-License-Identifier: GPL-2.0

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
#include "susfs.h"	/* susfs_expose_proc, sus_path_dirent_filter() */
#include "ksu_umount_gate.h"	/* susfs_is_current_proc_umounted_app (issue #34) */

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

static_assert(offsetof(struct stat, st_dev) == ST_DEV_OFF, "stat.st_dev");
static_assert(offsetof(struct stat, st_ino) == ST_INO_OFF, "stat.st_ino");
static_assert(offsetof(struct stat, st_nlink) == ST_NLINK_OFF, "stat.st_nlink");
static_assert(offsetof(struct stat, st_size) == ST_SIZE_OFF, "stat.st_size");
static_assert(offsetof(struct stat, st_blksize) == ST_BLKSIZE_OFF, "stat.st_blksize");
static_assert(offsetof(struct stat, st_blocks) == ST_BLOCKS_OFF, "stat.st_blocks");
static_assert(offsetof(struct stat, st_atime) == ST_ATIME_OFF, "stat.st_atime");
static_assert(offsetof(struct stat, st_mtime) == ST_MTIME_OFF, "stat.st_mtime");
static_assert(offsetof(struct stat, st_ctime) == ST_CTIME_OFF, "stat.st_ctime");

/* Upstream gates every sus_kstat read on susfs_is_current_proc_umounted_app(), exactly
 * (TIF_PROC_UMOUNTED && current_uid().val >= 10000).  KernelSU's setuid_hook sets that flag only
 * with the SUSFS integration compiled into the kernel, which this kernel has none of, so the flag
 * is asked of KernelSU itself instead: susfs_is_current_proc_umounted_app() answers it with
 * ksu_uid_should_umount() (ksu_umount_gate.h, issue #34).  The old `uid >= 10000` proxy spoofed for
 * every app uid - the manager and su-granted apps included.
 * Without any gate the spoofing would be visible to root too, wider than upstream.  Writers
 * (supercall, /proc) are configuration and stay ungated. */
static bool susfs_kstat_gate_ok(void)
{
	return susfs_is_current_proc_umounted_app();
}

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

struct kstat_call_counters {
	atomic_t calls;		/* this number returned 0: it reached the statbuf code */
	atomic_t ret_err;	/* this number returned -errno */
	atomic_t no_buf;	/* statbuf argument was NULL */
	atomic_t rewrite;	/* the buffer really changed */
	atomic_t miss_empty;	/* no rule registered at all */
	atomic_t miss_gate;	/* gate: not an app process KernelSU would umount modules for */
	atomic_t miss_lookup;	/* the (ino,dev) key matched no rule */
	atomic_t match_noflag;	/* matched, but this buffer has no field we impersonate */
	atomic_t uaccess;	/* copy_from_user/copy_to_user failed */
};

#define KSTAT_COUNTERS(nm)						\
	static struct kstat_call_counters cnt_##nm = {			\
		.calls = ATOMIC_INIT(0), .ret_err = ATOMIC_INIT(0),	\
		.no_buf = ATOMIC_INIT(0), .rewrite = ATOMIC_INIT(0),	\
		.miss_empty = ATOMIC_INIT(0), .miss_gate = ATOMIC_INIT(0),\
		.miss_lookup = ATOMIC_INIT(0), .match_noflag = ATOMIC_INIT(0),\
		.uaccess = ATOMIC_INIT(0),				\
	}

KSTAT_COUNTERS(nfstatat);
KSTAT_COUNTERS(nfstat);
KSTAT_COUNTERS(statx);
KSTAT_COUNTERS(fstatat64);
KSTAT_COUNTERS(stat64);
KSTAT_COUNTERS(lstat64);
KSTAT_COUNTERS(fstat64);

#define KSTAT_NR_SCAN_LO	106
#define KSTAT_NR_SCAN_HI	600
#define KSTAT_UNLISTED_SEEN	8

static atomic_t n_kstat_unlisted = ATOMIC_INIT(0);
static atomic_t kstat_unlisted_next = ATOMIC_INIT(0);
static long kstat_unlisted_seen[KSTAT_UNLISTED_SEEN];

static void kstat_note_unlisted(long nr)
{
	int slot;

	atomic_inc(&n_kstat_unlisted);
	slot = atomic_inc_return(&kstat_unlisted_next) - 1;
	kstat_unlisted_seen[slot % KSTAT_UNLISTED_SEEN] = nr;
}

struct kstat_call_state {
	struct kstat_call_counters *cnt;
	bool compat;
};

static bool susfs_kstat_spoof_statbuf(struct kstat_call_state *st, unsigned long statbuf)
{

	struct sus_kstat_snapshot snap;
	const struct sus_kstat_snapshot *e = &snap;
	unsigned long ino = 0, dev = 0;
	unsigned long v;
	unsigned int v32;
	long long v64;
	long sl;
	bool rewrote = false;

	if (susfs_kstat_table_empty()) {
		atomic_inc(&st->cnt->miss_empty);
		return false;
	}
	if (!susfs_kstat_gate_ok()) {
		atomic_inc(&st->cnt->miss_gate);
		return false;
	}

	if (copy_from_user(&ino, (void __user *)(statbuf + ST_INO_OFF), sizeof(ino))) {
		atomic_inc(&st->cnt->uaccess);
		return false;
	}
	if (copy_from_user(&dev, (void __user *)(statbuf + ST_DEV_OFF), sizeof(dev))) {
		atomic_inc(&st->cnt->uaccess);
		return false;
	}

	if (!susfs_kstat_lookup(ino, dev, &snap)) {
		atomic_inc(&st->cnt->miss_lookup);
		return false;
	}

	if (e->flags & KSTAT_SPOOF_INO) {
		v = e->spoofed_ino;
		if (copy_to_user((void __user *)(statbuf + ST_INO_OFF), &v, sizeof(v))) {
			atomic_inc(&st->cnt->uaccess);
			return false;
		}
		rewrote = true;
	}
	if (e->flags & KSTAT_SPOOF_DEV) {
		v = e->spoofed_dev;
		if (copy_to_user((void __user *)(statbuf + ST_DEV_OFF), &v, sizeof(v))) {
			atomic_inc(&st->cnt->uaccess);
			return false;
		}
		rewrote = true;
	}
	if (e->flags & KSTAT_SPOOF_NLINK) {
		v32 = e->spoofed_nlink;
		if (copy_to_user((void __user *)(statbuf + ST_NLINK_OFF), &v32, sizeof(v32))) {
			atomic_inc(&st->cnt->uaccess);
			return false;
		}
		rewrote = true;
	}
	if (e->flags & KSTAT_SPOOF_SIZE) {
		v64 = e->spoofed_size;
		if (copy_to_user((void __user *)(statbuf + ST_SIZE_OFF), &v64, sizeof(v64))) {
			atomic_inc(&st->cnt->uaccess);
			return false;
		}
		rewrote = true;
	}
	if (e->flags & KSTAT_SPOOF_BLKSIZE) {
		v32 = (unsigned int)e->spoofed_blksize;
		if (copy_to_user((void __user *)(statbuf + ST_BLKSIZE_OFF), &v32, sizeof(v32))) {
			atomic_inc(&st->cnt->uaccess);
			return false;
		}
		rewrote = true;
	}
	if (e->flags & KSTAT_SPOOF_BLOCKS) {
		v64 = e->spoofed_blocks;
		if (copy_to_user((void __user *)(statbuf + ST_BLOCKS_OFF), &v64, sizeof(v64))) {
			atomic_inc(&st->cnt->uaccess);
			return false;
		}
		rewrote = true;
	}
	if (e->flags & KSTAT_SPOOF_ATIME_TV_SEC) {
		sl = e->spoofed_atime_tv_sec;
		if (copy_to_user((void __user *)(statbuf + ST_ATIME_OFF), &sl, sizeof(sl))) {
			atomic_inc(&st->cnt->uaccess);
			return false;
		}
		rewrote = true;
	}
	if (e->flags & KSTAT_SPOOF_ATIME_TV_NSEC) {
		v = e->spoofed_atime_tv_nsec;
		if (copy_to_user((void __user *)(statbuf + ST_ATIME_NSEC_OFF), &v, sizeof(v))) {
			atomic_inc(&st->cnt->uaccess);
			return false;
		}
		rewrote = true;
	}
	if (e->flags & KSTAT_SPOOF_MTIME_TV_SEC) {
		sl = e->spoofed_mtime_tv_sec;
		if (copy_to_user((void __user *)(statbuf + ST_MTIME_OFF), &sl, sizeof(sl))) {
			atomic_inc(&st->cnt->uaccess);
			return false;
		}
		rewrote = true;
	}
	if (e->flags & KSTAT_SPOOF_MTIME_TV_NSEC) {
		v = e->spoofed_mtime_tv_nsec;
		if (copy_to_user((void __user *)(statbuf + ST_MTIME_NSEC_OFF), &v, sizeof(v))) {
			atomic_inc(&st->cnt->uaccess);
			return false;
		}
		rewrote = true;
	}
	if (e->flags & KSTAT_SPOOF_CTIME_TV_SEC) {
		sl = e->spoofed_ctime_tv_sec;
		if (copy_to_user((void __user *)(statbuf + ST_CTIME_OFF), &sl, sizeof(sl))) {
			atomic_inc(&st->cnt->uaccess);
			return false;
		}
		rewrote = true;
	}
	if (e->flags & KSTAT_SPOOF_CTIME_TV_NSEC) {
		v = e->spoofed_ctime_tv_nsec;
		if (copy_to_user((void __user *)(statbuf + ST_CTIME_NSEC_OFF), &v, sizeof(v))) {
			atomic_inc(&st->cnt->uaccess);
			return false;
		}
		rewrote = true;
	}

	if (!rewrote)
		atomic_inc(&st->cnt->match_noflag);
	else
		atomic_inc(&st->cnt->rewrite);
	return rewrote;
}

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

/* AArch32 stat numbers, from the 32-bit ARM table (arch/arm/tools/syscall.tbl) - an arm64 tree
 * has no macro for them.  They are only reached for a task running that ABI: arm64's native
 * 195/196/197 are shmctl/shmat/shmdt (whose second argument is an address or a small integer,
 * not a statbuf) and its native 79/80 are newfstatat/fstat, which AArch32 numbers 79/80 give to
 * settimeofday/getgroups. */
#define COMPAT_FSTATAT64_NR	327	/* fstatat64(dfd, path, statbuf, flag) */
#define COMPAT_STAT64_NR	195	/* stat64(path, statbuf) */
#define COMPAT_LSTAT64_NR	196	/* lstat64(path, statbuf) */
#define COMPAT_FSTAT64_NR	197	/* fstat64(fd, statbuf) */

struct kstat_nr_entry {
	long nr;
	const char *name;
	struct kstat_call_counters *cnt;
};

static struct kstat_nr_entry kstat_nr_table[] = {
	{ __NR_newfstatat, "newfstatat", &cnt_nfstatat },
	{ __NR_fstat,      "fstat",      &cnt_nfstat },
	{ __NR_statx,      "statx",      &cnt_statx },
	{ COMPAT_FSTATAT64_NR, "fstatat64/compat", &cnt_fstatat64 },
	{ COMPAT_STAT64_NR,    "stat64/compat",    &cnt_stat64 },
	{ COMPAT_LSTAT64_NR,   "lstat64/compat",   &cnt_lstat64 },
	{ COMPAT_FSTAT64_NR,   "fstat64/compat",   &cnt_fstat64 },
};

/* compat (32-bit) statbuf: struct stat64 (see above) - the layout all four handled syscalls use. */
static bool susfs_kstat_spoof_compat_statbuf(struct kstat_call_state *st, unsigned long statbuf)
{
	struct sus_kstat_snapshot snap;
	const struct sus_kstat_snapshot *e = &snap;
	unsigned long long v64;
	unsigned int ino = 0, dev = 0;
	unsigned int v32;
	int v;
	bool rewrote = false;

	if (susfs_kstat_table_empty()) {
		atomic_inc(&st->cnt->miss_empty);
		return false;
	}
	if (!susfs_kstat_gate_ok()) {
		atomic_inc(&st->cnt->miss_gate);
		return false;
	}

	if (copy_from_user(&ino, (void __user *)(statbuf + STAT64_ST_BROKEN_INO_OFF), sizeof(ino))) {
		atomic_inc(&st->cnt->uaccess);
		return false;
	}
	if (copy_from_user(&dev, (void __user *)(statbuf + STAT64_ST_DEV_OFF), sizeof(dev))) {
		atomic_inc(&st->cnt->uaccess);
		return false;
	}
	if (!susfs_kstat_lookup(ino, dev, &snap)) {
		atomic_inc(&st->cnt->miss_lookup);
		return false;
	}

	if (e->flags & KSTAT_SPOOF_INO) {
		v32 = (unsigned int)e->spoofed_ino;
		if (copy_to_user((void __user *)(statbuf + STAT64_ST_BROKEN_INO_OFF), &v32, sizeof(v32))) {
			atomic_inc(&st->cnt->uaccess);
			return false;
		}
		v64 = (unsigned long long)e->spoofed_ino;
		if (copy_to_user((void __user *)(statbuf + STAT64_ST_INO_OFF), &v64, sizeof(v64))) {
			atomic_inc(&st->cnt->uaccess);
			return false;
		}
		rewrote = true;
	}
	if (e->flags & KSTAT_SPOOF_DEV) {
		v64 = (unsigned long long)e->spoofed_dev;
		if (copy_to_user((void __user *)(statbuf + STAT64_ST_DEV_OFF), &v64, sizeof(v64))) {
			atomic_inc(&st->cnt->uaccess);
			return false;
		}
		rewrote = true;
	}
	if (e->flags & KSTAT_SPOOF_NLINK) {
		v32 = (unsigned int)e->spoofed_nlink;
		if (copy_to_user((void __user *)(statbuf + STAT64_ST_NLINK_OFF), &v32, sizeof(v32))) {
			atomic_inc(&st->cnt->uaccess);
			return false;
		}
		rewrote = true;
	}
	if (e->flags & KSTAT_SPOOF_SIZE) {
		v64 = (unsigned long long)e->spoofed_size;
		if (copy_to_user((void __user *)(statbuf + STAT64_ST_SIZE_OFF), &v64, sizeof(v64))) {
			atomic_inc(&st->cnt->uaccess);
			return false;
		}
		rewrote = true;
	}
	if (e->flags & KSTAT_SPOOF_BLKSIZE) {
		v32 = (unsigned int)e->spoofed_blksize;
		if (copy_to_user((void __user *)(statbuf + STAT64_ST_BLKSIZE_OFF), &v32, sizeof(v32))) {
			atomic_inc(&st->cnt->uaccess);
			return false;
		}
		rewrote = true;
	}
	if (e->flags & KSTAT_SPOOF_BLOCKS) {
		v64 = (unsigned long long)e->spoofed_blocks;
		if (copy_to_user((void __user *)(statbuf + STAT64_ST_BLOCKS_OFF), &v64, sizeof(v64))) {
			atomic_inc(&st->cnt->uaccess);
			return false;
		}
		rewrote = true;
	}
	if (e->flags & KSTAT_SPOOF_ATIME_TV_SEC) {
		v = (int)e->spoofed_atime_tv_sec;
		if (copy_to_user((void __user *)(statbuf + STAT64_ST_ATIME_OFF), &v, sizeof(v))) {
			atomic_inc(&st->cnt->uaccess);
			return false;
		}
		rewrote = true;
	}
	if (e->flags & KSTAT_SPOOF_ATIME_TV_NSEC) {
		v32 = (unsigned int)e->spoofed_atime_tv_nsec;
		if (copy_to_user((void __user *)(statbuf + STAT64_ST_ATIME_NSEC_OFF), &v32, sizeof(v32))) {
			atomic_inc(&st->cnt->uaccess);
			return false;
		}
		rewrote = true;
	}
	if (e->flags & KSTAT_SPOOF_MTIME_TV_SEC) {
		v = (int)e->spoofed_mtime_tv_sec;
		if (copy_to_user((void __user *)(statbuf + STAT64_ST_MTIME_OFF), &v, sizeof(v))) {
			atomic_inc(&st->cnt->uaccess);
			return false;
		}
		rewrote = true;
	}
	if (e->flags & KSTAT_SPOOF_MTIME_TV_NSEC) {
		v32 = (unsigned int)e->spoofed_mtime_tv_nsec;
		if (copy_to_user((void __user *)(statbuf + STAT64_ST_MTIME_NSEC_OFF), &v32, sizeof(v32))) {
			atomic_inc(&st->cnt->uaccess);
			return false;
		}
		rewrote = true;
	}
	if (e->flags & KSTAT_SPOOF_CTIME_TV_SEC) {
		v = (int)e->spoofed_ctime_tv_sec;
		if (copy_to_user((void __user *)(statbuf + STAT64_ST_CTIME_OFF), &v, sizeof(v))) {
			atomic_inc(&st->cnt->uaccess);
			return false;
		}
		rewrote = true;
	}
	if (e->flags & KSTAT_SPOOF_CTIME_TV_NSEC) {
		v32 = (unsigned int)e->spoofed_ctime_tv_nsec;
		if (copy_to_user((void __user *)(statbuf + STAT64_ST_CTIME_NSEC_OFF), &v32, sizeof(v32))) {
			atomic_inc(&st->cnt->uaccess);
			return false;
		}
		rewrote = true;
	}

	if (!rewrote)
		atomic_inc(&st->cnt->match_noflag);
	else
		atomic_inc(&st->cnt->rewrite);
	return rewrote;
}

#define STATX_F_INO		STATX_INO
#define STATX_F_NLINK		STATX_NLINK
#define STATX_F_SIZE		STATX_SIZE
#define STATX_F_BLOCKS		STATX_BLOCKS

struct susfs_statx_offs {
	unsigned short dev, ino, nlink, size, blksize, blocks;
	unsigned short atime_sec, atime_nsec, mtime_sec, mtime_nsec,
		       ctime_sec, ctime_nsec, mask;
};

static const struct susfs_statx_offs kstat_statx_offs = {
	.dev = offsetof(struct statx, stx_dev_major),
	.ino = offsetof(struct statx, stx_ino),
	.nlink = offsetof(struct statx, stx_nlink),
	.size = offsetof(struct statx, stx_size),
	.blksize = offsetof(struct statx, stx_blksize),
	.blocks = offsetof(struct statx, stx_blocks),
	.atime_sec = offsetof(struct statx, stx_atime),
	.atime_nsec = offsetof(struct statx, stx_atime) + offsetof(struct timespec64, tv_nsec),
	.mtime_sec = offsetof(struct statx, stx_mtime),
	.mtime_nsec = offsetof(struct statx, stx_mtime) + offsetof(struct timespec64, tv_nsec),
	.ctime_sec = offsetof(struct statx, stx_ctime),
	.ctime_nsec = offsetof(struct statx, stx_ctime) + offsetof(struct timespec64, tv_nsec),
	.mask = offsetof(struct statx, stx_mask),
};

static_assert(offsetof(struct statx, stx_mask) == 0x00, "statx.stx_mask");
static_assert(offsetof(struct statx, stx_blksize) == 0x04, "statx.stx_blksize");
static_assert(offsetof(struct statx, stx_attributes) == 0x08, "statx.stx_attributes");
static_assert(offsetof(struct statx, stx_nlink) == 0x10, "statx.stx_nlink");
static_assert(offsetof(struct statx, stx_ino) == 0x20, "statx.stx_ino");
static_assert(offsetof(struct statx, stx_size) == 0x28, "statx.stx_size");
static_assert(offsetof(struct statx, stx_blocks) == 0x30, "statx.stx_blocks");
static_assert(offsetof(struct statx, stx_atime) == 0x40, "statx.stx_atime");
static_assert(offsetof(struct statx, stx_btime) == 0x50, "statx.stx_btime");
static_assert(offsetof(struct statx, stx_ctime) == 0x60, "statx.stx_ctime");
static_assert(offsetof(struct statx, stx_mtime) == 0x70, "statx.stx_mtime");

static_assert(offsetof(struct statx, stx_dev_major) == 0x88, "statx.stx_dev_major");
static_assert(offsetof(struct statx, stx_dev_minor) == 0x8c, "statx.stx_dev_minor");
static_assert(offsetof(struct statx, stx_mnt_id) == 0x90, "statx.stx_mnt_id");
static_assert(sizeof(struct statx) == 256, "statx size");
static_assert(sizeof(((struct statx *)0)->stx_ino) == 8, "statx stx_ino is u64");
static_assert(sizeof(((struct statx *)0)->stx_size) == 8, "statx stx_size is u64");

/* Read a field of the buffer, write the spoofed value back only when the mask carries the field. */
#define STATX_FIELD_U64(off, val, mbit)						\
	do {									\
		if (eff & (mbit)) {						\
			u64 __v = (u64)(val);					\
										\
			if (copy_to_user((void __user *)(sbuf + (off)), &__v,	\
					 sizeof(__v))) {			\
				atomic_inc(&st->cnt->uaccess);			\
				return false;					\
			}							\
			rewrote = true;						\
		}								\
	} while (0)

#define STATX_FIELD_S32(off, val, mbit)						\
	do {									\
		if (eff & (mbit)) {						\
			s32 __v = (s32)(val);					\
			u32 __u = (u32)__v;					\
										\
			if (copy_to_user((void __user *)(sbuf + (off)), &__u,	\
					 sizeof(__u))) {			\
				atomic_inc(&st->cnt->uaccess);			\
				return false;					\
			}							\
			rewrote = true;						\
		}								\
	} while (0)

#define STATX_FIELD_U32(off, val, mbit)						\
	do {									\
		if (eff & (mbit)) {						\
			u32 __v = (u32)(val);					\
										\
			if (copy_to_user((void __user *)(sbuf + (off)), &__v,	\
					 sizeof(__v))) {			\
				atomic_inc(&st->cnt->uaccess);			\
				return false;					\
			}							\
			rewrote = true;						\
		}								\
	} while (0)

/* returns true when the buffer was really changed */
static bool susfs_kstat_spoof_statx(struct kstat_call_state *st, unsigned long sbuf,
				    u32 req_mask)
{
	const struct susfs_statx_offs *o = &kstat_statx_offs;
	struct sus_kstat_snapshot snap;
	const struct sus_kstat_snapshot *e = &snap;
	unsigned long ino = 0;
	unsigned int dev = 0;
	u32 buf_mask = 0, eff;
	bool rewrote = false;

	if (susfs_kstat_table_empty()) {
		atomic_inc(&st->cnt->miss_empty);
		return false;
	}
	if (!susfs_kstat_gate_ok()) {
		atomic_inc(&st->cnt->miss_gate);
		return false;
	}

	if (copy_from_user(&ino, (void __user *)(sbuf + o->ino), sizeof(ino))) {
		atomic_inc(&st->cnt->uaccess);
		return false;
	}
	if (copy_from_user(&dev, (void __user *)(sbuf + o->dev), sizeof(dev))) {
		atomic_inc(&st->cnt->uaccess);
		return false;
	}
	if (copy_from_user(&buf_mask, (void __user *)(sbuf + o->mask), sizeof(buf_mask))) {
		atomic_inc(&st->cnt->uaccess);
		return false;
	}

	if (!susfs_kstat_lookup(ino, dev, &snap)) {
		atomic_inc(&st->cnt->miss_lookup);
		return false;
	}

	eff = req_mask | buf_mask;

	if (e->flags & KSTAT_SPOOF_INO)
		STATX_FIELD_U64(o->ino, e->spoofed_ino, STATX_F_INO);
	if (e->flags & KSTAT_SPOOF_NLINK)
		STATX_FIELD_U32(o->nlink, e->spoofed_nlink, STATX_F_NLINK);
	if (e->flags & KSTAT_SPOOF_SIZE)
		STATX_FIELD_U64(o->size, e->spoofed_size, STATX_F_SIZE);
	if (e->flags & KSTAT_SPOOF_BLOCKS)
		STATX_FIELD_U64(o->blocks, e->spoofed_blocks, STATX_F_BLOCKS);

	if (e->flags & KSTAT_SPOOF_BLKSIZE) {
		s32 v = (s32)e->spoofed_blksize;

		if (copy_to_user((void __user *)(sbuf + o->blksize), &v, sizeof(v))) {
			atomic_inc(&st->cnt->uaccess);
			return false;
		}
		rewrote = true;
	}
	if (e->flags & KSTAT_SPOOF_ATIME_TV_SEC)
		STATX_FIELD_S32(o->atime_sec, e->spoofed_atime_tv_sec, STATX_ATIME);
	if (e->flags & KSTAT_SPOOF_ATIME_TV_NSEC)
		STATX_FIELD_U32(o->atime_nsec, e->spoofed_atime_tv_nsec, STATX_ATIME);
	if (e->flags & KSTAT_SPOOF_MTIME_TV_SEC)
		STATX_FIELD_S32(o->mtime_sec, e->spoofed_mtime_tv_sec, STATX_MTIME);
	if (e->flags & KSTAT_SPOOF_MTIME_TV_NSEC)
		STATX_FIELD_U32(o->mtime_nsec, e->spoofed_mtime_tv_nsec, STATX_MTIME);
	if (e->flags & KSTAT_SPOOF_CTIME_TV_SEC)
		STATX_FIELD_S32(o->ctime_sec, e->spoofed_ctime_tv_sec, STATX_CTIME);
	if (e->flags & KSTAT_SPOOF_CTIME_TV_NSEC)
		STATX_FIELD_U32(o->ctime_nsec, e->spoofed_ctime_tv_nsec, STATX_CTIME);

	if ((e->flags & KSTAT_SPOOF_DEV) && (eff & STATX_BASIC_STATS)) {
		unsigned int enc = (unsigned int)e->spoofed_dev;

		u16 maj = (u16)((enc & 0xfff00u) >> 8);
		u16 min = (u16)MINOR(new_decode_dev(enc));

		if (copy_to_user((void __user *)(sbuf + o->dev), &maj, sizeof(maj))) {
			atomic_inc(&st->cnt->uaccess);
			return false;
		}
		if (copy_to_user((void __user *)(sbuf + o->dev + 4), &min, sizeof(min))) {
			atomic_inc(&st->cnt->uaccess);
			return false;
		}
		rewrote = true;
	}

	if (!rewrote) {
		atomic_inc(&st->cnt->match_noflag);
		return false;
	}

	atomic_inc(&st->cnt->rewrite);
	return true;
}

static void kstat_sys_exit(void *data, struct pt_regs *regs, long ret)
{
	unsigned long args[6];
	struct kstat_call_counters *c;
	struct kstat_call_state st;
	long nr = syscall_get_nr(current, regs);
	bool compat = is_compat_task();
	int lay = sus_path_dirent_layout_id(nr, compat);

	if (lay >= 0) {
		long rc;

		/* The number alone does not identify the call (native 141 is getpriority, not
		 * the AArch32 getdents): sus_path_dirent_layout_id() gates it on the ABI, so
		 * anything that is not really a listing leaves here before the arguments are
		 * read. */
		if (ret <= 0) {
			sus_path_dirent_filter(lay, 0, ret);
			return;
		}
		syscall_get_arguments(current, regs, args);
		rc = sus_path_dirent_filter(lay,
					    compat ? (unsigned long)compat_ptr((u32)args[1])
						   : args[1],
					    ret);
		if (rc != ret)
			syscall_set_return_value(current, regs, 0, rc);
		return;
	}

	/* ---- stat family: number -> counters -> argument positions ----
	 * Gated on the ABI for the same reason as the listing numbers above: on arm64 the native
	 * table's 195/196/197 are shmctl/shmat/shmdt, and shmat's second argument is a mapped
	 * address - read as a compat struct stat64 buffer it would hand back whatever the caller
	 * happens to have there, and on a rule hit rewrite it. */
	if (compat) {
		switch (nr) {
		case COMPAT_FSTATAT64_NR:
			c = &cnt_fstatat64;
			break;
		case COMPAT_STAT64_NR:
			c = &cnt_stat64;
			break;
		case COMPAT_LSTAT64_NR:
			c = &cnt_lstat64;
			break;
		case COMPAT_FSTAT64_NR:
			c = &cnt_fstat64;
			break;
		default:
			c = NULL;
			break;
		}
	} else {
		switch (nr) {
		case __NR_newfstatat:
			c = &cnt_nfstatat;
			break;
		case __NR_fstat:
			/* fstat(fd, statbuf): the buffer is args[1], not args[2]. */
			c = &cnt_nfstat;
			break;
		case __NR_statx:
			c = &cnt_statx;
			break;
		default:
			c = NULL;
			break;
		}
	}

	if (!c) {
		/* A listing number cannot reach this point any more: the gate at the top of this
		 * function answers both getdents ABIs before the stat switch, so only the stat
		 * range is worth noting here. */
		if (nr >= KSTAT_NR_SCAN_LO && nr <= KSTAT_NR_SCAN_HI)
			kstat_note_unlisted(nr);
		return;
	}

	/* Whitelisted: from here on only this number's counters move. */
	if (ret != 0) {
		atomic_inc(&c->ret_err);
		return;
	}
	atomic_inc(&c->calls);

	st.cnt = c;
	st.compat = compat;	/* the ABI that selected the number above */

	/* Argument positions differ per number, so this stays a number switch - but only numbers
	 * the gate above selected for THIS ABI can reach it, and the two ABIs' number sets
	 * (79/80/291 native, 195/196/197/327 compat) do not overlap, so it needs no gate of its
	 * own. */
	switch (nr) {
	case __NR_newfstatat:
		syscall_get_arguments(current, regs, args);
		if (!args[2]) {
			atomic_inc(&c->no_buf);
			return;
		}
		susfs_kstat_spoof_statbuf(&st, args[2]);
		return;
	case __NR_fstat:
		syscall_get_arguments(current, regs, args);
		if (!args[1]) {
			atomic_inc(&c->no_buf);
			return;
		}
		susfs_kstat_spoof_statbuf(&st, args[1]);
		return;
	case __NR_statx:

		syscall_get_arguments(current, regs, args);
		if (!args[4]) {
			atomic_inc(&c->no_buf);
			return;
		}
		susfs_kstat_spoof_statx(&st,
			st.compat ? (unsigned long)compat_ptr((u32)args[4]) : args[4],
			(u32)args[3]);
		return;
	case COMPAT_FSTATAT64_NR:

		syscall_get_arguments(current, regs, args);
		if (!args[2]) {
			atomic_inc(&c->no_buf);
			return;
		}
		susfs_kstat_spoof_compat_statbuf(&st, (unsigned long)compat_ptr((u32)args[2]));
		return;
	case COMPAT_STAT64_NR:
	case COMPAT_LSTAT64_NR:
	case COMPAT_FSTAT64_NR:

		syscall_get_arguments(current, regs, args);
		if (!args[1]) {
			atomic_inc(&c->no_buf);
			return;
		}
		susfs_kstat_spoof_compat_statbuf(&st, (unsigned long)compat_ptr((u32)args[1]));
		return;
	}
}

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

static int susfs_kstat_fill_from_path(struct sus_kstat_entry *e, const char *path)
{
	struct path p;
	struct inode *inode;
	int err;
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 6, 0)

	struct timespec64 ctime;
#endif
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 12, 0)

	struct timespec64 atime, mtime;
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
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 12, 0)
	atime = inode_get_atime(inode);
	mtime = inode_get_mtime(inode);
#endif

	e->target_ino = inode->i_ino;
	e->target_dev = new_encode_dev(inode->i_sb->s_dev);
	e->spoofed_ino = inode->i_ino;
	e->spoofed_dev = new_encode_dev(inode->i_sb->s_dev);
	e->spoofed_nlink = inode->i_nlink;
	e->spoofed_size = inode->i_size;
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 12, 0)
	e->spoofed_atime_tv_sec = atime.tv_sec;
	e->spoofed_atime_tv_nsec = atime.tv_nsec;
	e->spoofed_mtime_tv_sec = mtime.tv_sec;
	e->spoofed_mtime_tv_nsec = mtime.tv_nsec;
#else
	e->spoofed_atime_tv_sec = inode->i_atime.tv_sec;
	e->spoofed_atime_tv_nsec = inode->i_atime.tv_nsec;
	e->spoofed_mtime_tv_sec = inode->i_mtime.tv_sec;
	e->spoofed_mtime_tv_nsec = inode->i_mtime.tv_nsec;
#endif
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

	static const unsigned int f_flags[12] = {
		KSTAT_SPOOF_INO, KSTAT_SPOOF_DEV, KSTAT_SPOOF_NLINK,
		KSTAT_SPOOF_SIZE, KSTAT_SPOOF_ATIME_TV_SEC,
		KSTAT_SPOOF_ATIME_TV_NSEC, KSTAT_SPOOF_MTIME_TV_SEC,
		KSTAT_SPOOF_MTIME_TV_NSEC, KSTAT_SPOOF_CTIME_TV_SEC,
		KSTAT_SPOOF_CTIME_TV_NSEC, KSTAT_SPOOF_BLOCKS,
		KSTAT_SPOOF_BLKSIZE,
	};
	const char *path = argv[1];

	/* argv[2 + i] below reaches argv[13], so this needs argv[14]: assert it here and not only at
	 * the call site, whose `argc == 14` check is against a 16-slot argv. */
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

int susfs_kstat_init(void)
{
	int rc;

	rc = register_trace_sys_exit(kstat_sys_exit, NULL);
	if (rc)
		pr_warn("register_trace_sys_exit failed %d\n", rc);
	else
		kstat_tp_registered = true;

	if (susfs_control_node_allowed()) {
		kstat_proc_entry = proc_create("susfs_kstat", 0777, NULL,
					       &kstat_proc_ops);
		if (!kstat_proc_entry)
			pr_warn("proc_create(susfs_kstat) failed\n");
	} else {
		SUSFS_LOGI("susfs_kstat: /proc node not created (expose_proc=%d lsm=%d)\n",
			(int)susfs_expose_proc, (int)sus_path_lsm_active());
	}

	SUSFS_LOGI("kstat armed: %d rules (sys_exit tp=%d proc=%d); stat rewrite + sus_path dirent rewrite ride that one tracepoint\n",
		nkstat, kstat_tp_registered, kstat_proc_entry != NULL);
	return 0;
}

void susfs_kstat_exit(void)
{
	kstat_maps_disarm();

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

	seq_printf(m, "maps: armed=%d hits=%d rewrites=%d\n",
		   kstat_maps_registered, atomic_read(&n_kstat_map_hits),
		   atomic_read(&n_kstat_map_rewrites));

	{
		unsigned int i;

		for (i = 0; i < ARRAY_SIZE(kstat_nr_table); i++) {
			struct kstat_call_counters *c = kstat_nr_table[i].cnt;

			seq_printf(m,
				   "stat nr %-16s (%ld): ok=%d rw=%d | err=%d nobuf=%d empty=%d gate=%d lookup=%d noflag=%d uacc=%d\n",
				   kstat_nr_table[i].name, kstat_nr_table[i].nr,
				   atomic_read(&c->calls), atomic_read(&c->rewrite),
				   atomic_read(&c->ret_err), atomic_read(&c->no_buf),
				   atomic_read(&c->miss_empty), atomic_read(&c->miss_gate),
				   atomic_read(&c->miss_lookup), atomic_read(&c->match_noflag),
				   atomic_read(&c->uaccess));
		}
		seq_printf(m, "stat unlisted-nr hits=%d (stat-range numbers the dispatcher did not know: last %d seen: %ld %ld %ld %ld %ld %ld %ld %ld)\n",
			   atomic_read(&n_kstat_unlisted), (int)KSTAT_UNLISTED_SEEN,
			   kstat_unlisted_seen[0], kstat_unlisted_seen[1],
			   kstat_unlisted_seen[2], kstat_unlisted_seen[3],
			   kstat_unlisted_seen[4], kstat_unlisted_seen[5],
			   kstat_unlisted_seen[6], kstat_unlisted_seen[7]);
	}

	{
		char line[512];
		int n = sus_path_dirent_stat_line(line, sizeof(line));

		if (n > 0)
			seq_write(m, line, min_t(int, n, (int)sizeof(line) - 1));
	}
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

		return err;
	}
	return len;
}
