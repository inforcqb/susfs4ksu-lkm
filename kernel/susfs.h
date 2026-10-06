/* SPDX-License-Identifier: GPL-2.0 */
#ifndef __SUSFS_H
#define __SUSFS_H

#include <linux/string.h>
#include <linux/err.h>	/* IS_ERR */
#include <linux/mm.h>	/* PAGE_SIZE */

static inline bool susfs_ptr_plausible(const void *p)
{
	return (unsigned long)p >= PAGE_SIZE && !IS_ERR(p);
}

static inline bool susfs_abi_path_ok(const char *field, size_t size)
{
	return strnlen(field, size) < size;
}

/* Add a path to sus_path's hidden set from kernel code (no supercall needed); returns 0 or negative errno. */
int sus_path_add_hidden(const char *path);

int sus_path_add_self_hidden(const char *path);

int sus_path_del_path(const char *path);

/* -1 when this syscall number, for a task running that ABI, is not a directory listing. */
int sus_path_dirent_layout_id(long syscall_nr, bool compat);

long sus_path_dirent_filter(int lay_id, unsigned long buf, long ret);

int sus_path_dirent_stat_line(char *buf, size_t size);

#define SUSFS_LKM_MODULE_NAME "susfs_guard_lkm"
#define SUSFS_LKM_SYSFS_DIR   "/sys/module/" SUSFS_LKM_MODULE_NAME

#define SUSFS_HIDE_MODULES_NODE "/proc/susfs_hide_modules"
bool susfs_hide_modules_active(void);

/* The sus_mount control node: decides WHICH mounts count as ours (the on/off switch stays the hide_sus_mnts_for_non_su_procs supercall); root-only, ENOENT for everyone else through sus_path. */
#define SUSFS_HIDE_MOUNTS_NODE "/proc/susfs_hide_mounts"
bool susfs_hide_modules_node_ready(void);

#define SUSFS_PATH_NODE "/proc/susfs_path"

extern bool susfs_expose_proc;

/* feature init/exit (each feature is its own translation unit) */
int susfs_uname_init(void);
void susfs_uname_exit(void);

int susfs_kstat_init(void);
void susfs_kstat_exit(void);

int susfs_sus_map_init(void);
void susfs_sus_map_exit(void);

int sus_path_init(void);
void sus_path_exit(void);

int susfs_sus_mount_init(void);
void susfs_sus_mount_exit(void);

int susfs_spoof_cmdline_init(void);
void susfs_spoof_cmdline_exit(void);

int susfs_open_redirect_init(void);
void susfs_open_redirect_exit(void);

int susfs_enable_log_init(void);
void susfs_enable_log_exit(void);
bool susfs_log_enabled(void);

int susfs_avc_spoof_init(void);
void susfs_avc_spoof_exit(void);

int susfs_supercall_init(void);
void susfs_supercall_exit(void);

/* feature supercall handlers (upstream signature: void xxx(void __user **arg)) */
void susfs_uname_supercall(void __user **arg);
void susfs_enable_log_supercall(void __user **arg);
void susfs_avc_spoof_supercall(void __user **arg);
void susfs_spoof_cmdline_supercall(void __user **arg);
void susfs_sus_map_supercall(void __user **arg);
void sus_path_supercall(unsigned int cmd, void __user **arg);
void susfs_kstat_supercall(unsigned int cmd, void __user **arg);
void susfs_open_redirect_supercall(void __user **arg);
void susfs_sus_mount_supercall(void __user **arg);

int susfs_hide_syms_init(void);
void susfs_hide_syms_exit(void);

bool susfs_hide_syms_active(void);
bool sus_path_lsm_active(void);

static inline bool susfs_control_node_allowed(void)
{
	return susfs_expose_proc && sus_path_lsm_active();
}

bool susfs_open_redirect_spoof_ids(unsigned long ino, unsigned long *out_ino, unsigned long *out_mnt_id);

#endif
