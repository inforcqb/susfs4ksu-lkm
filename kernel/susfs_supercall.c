// SPDX-License-Identifier: GPL-2.0

#include <linux/module.h>
#include <linux/kprobes.h>
#include <linux/task_work.h>
#include <linux/slab.h>
#include <linux/uaccess.h>
#include <linux/cred.h>
#include <linux/syscalls.h>
#include <linux/string.h>
#include "susfs_abi.h"
#include "susfs_log.h"
#include "susfs.h"

struct susfs_tw {
	struct callback_head cb;
	unsigned int cmd;
	void __user *payload;   /* points at the userspace payload struct */
};

static void susfs_show_version(void __user **arg)
{
	struct st_susfs_version info = {0};

	if (copy_from_user(&info, (void __user *)*arg, sizeof(info))) {
		info.err = -EFAULT;
		goto out;
	}
	strscpy(info.susfs_version, SUSFS_VERSION_STR, SUSFS_MAX_VERSION_BUFSIZE);
	info.err = 0;
out:
	if (copy_to_user((void __user *)*arg, &info, sizeof(info)))
		pr_warn("susfs show_version copy_to_user failed\n");
}

static void susfs_show_variant(void __user **arg)
{
	struct st_susfs_variant info = {0};

	if (copy_from_user(&info, (void __user *)*arg, sizeof(info))) {
		info.err = -EFAULT;
		goto out;
	}
	strscpy(info.susfs_variant, SUSFS_VARIANT_STR, SUSFS_MAX_VARIANT_BUFSIZE);
	info.err = 0;
out:
	if (copy_to_user((void __user *)*arg, &info, sizeof(info)))
		pr_warn("susfs show_variant copy_to_user failed\n");
}

/* List every feature this LKM implements: the first line marks the source (an LKM, not a built-in
 * SUSFS) and the rest use upstream CONFIG macro names.  Entries with an `active` callback are
 * reported only while the feature is really installed: advertising a feature whose registration
 * failed is the exact inconsistency a detector probes for, so failing ones are omitted (and logged
 * by their init). */
struct feature_entry {
	const char *name;
	bool (*active)(void);	/* NULL = always present */
};

static const struct feature_entry enabled_features[] = {
	/* First line, and deliberately not a CONFIG_* name: the caller has to be able to tell this
	 * list apart from a built-in SUSFS's, whose features live in the kernel image and have a
	 * different lifecycle (no load/unload, no /sys/module entry, no module parameters). */
	{ "SUSFS_LKM_MODULES\n",		NULL },
	{ "CONFIG_KSU_SUSFS_SUS_PATH\n",	sus_path_lsm_active },
	{ "CONFIG_KSU_SUSFS_SUS_MOUNT\n",	NULL },
	{ "CONFIG_KSU_SUSFS_SUS_KSTAT\n",	NULL },
	{ "CONFIG_KSU_SUSFS_SPOOF_UNAME\n",	NULL },
	{ "CONFIG_KSU_SUSFS_ENABLE_LOG\n",	NULL },
	{ "CONFIG_KSU_SUSFS_HIDE_KSU_SUSFS_SYMBOLS\n",	susfs_hide_syms_active },
	{ "CONFIG_KSU_SUSFS_SPOOF_CMDLINE_OR_BOOTCONFIG\n", NULL },
	{ "CONFIG_KSU_SUSFS_OPEN_REDIRECT\n",	NULL },
	{ "CONFIG_KSU_SUSFS_SUS_MAP\n",		NULL },
	/* hide_modules is not upstream's, so it is not listed here - the feature itself is unchanged. */
};

static struct st_susfs_enabled_features susfs_enabled_features_nomem;

static void susfs_show_enabled_features(void __user **arg)
{
	struct st_susfs_enabled_features *info;
	size_t off = 0;
	int i;

	info = kzalloc(sizeof(*info), GFP_KERNEL);
	if (!info) {

		susfs_enabled_features_nomem.err = -ENOMEM;
		if (copy_to_user((void __user *)*arg, &susfs_enabled_features_nomem,
				 sizeof(susfs_enabled_features_nomem)))
			pr_warn("susfs show_enabled_features copy_to_user failed\n");
		pr_warn_ratelimited("susfs: show_enabled_features kzalloc failed, reported -ENOMEM\n");
		return;
	}

	for (i = 0; i < ARRAY_SIZE(enabled_features); i++) {
		const char *name = enabled_features[i].name;
		size_t len = strlen(name);

		if (enabled_features[i].active && !enabled_features[i].active())
			continue;
		if (off + len >= SUSFS_ENABLED_FEATURES_SIZE)
			break;
		memcpy(info->enabled_features + off, name, len);
		off += len;
	}
	info->err = 0;

	if (copy_to_user((void __user *)*arg, info, sizeof(*info)))
		pr_warn("susfs show_enabled_features copy_to_user failed\n");
	kfree(info);
}

static void susfs_tw_func(struct callback_head *cb)
{
	struct susfs_tw *tw = container_of(cb, struct susfs_tw, cb);
	void __user *arg = tw->payload;

	switch (tw->cmd) {
	case CMD_SUSFS_SHOW_VERSION:
		susfs_show_version(&arg);
		break;
	case CMD_SUSFS_SHOW_VARIANT:
		susfs_show_variant(&arg);
		break;
	case CMD_SUSFS_SHOW_ENABLED_FEATURES:
		susfs_show_enabled_features(&arg);
		break;
	case CMD_SUSFS_ADD_SUS_PATH:
	case CMD_SUSFS_ADD_SUS_PATH_LOOP:
		/* The two commands answer a missing path differently upstream. */
		sus_path_supercall(tw->cmd, &arg);
		break;
	case CMD_SUSFS_ADD_SUS_MAP:
		susfs_sus_map_supercall(&arg);
		break;
	case CMD_SUSFS_ADD_SUS_KSTAT:
	case CMD_SUSFS_UPDATE_SUS_KSTAT:
	case CMD_SUSFS_ADD_SUS_KSTAT_STATICALLY:
		susfs_kstat_supercall(tw->cmd, &arg);
		break;
	case CMD_SUSFS_SET_UNAME:
		susfs_uname_supercall(&arg);
		break;
	case CMD_SUSFS_ENABLE_LOG:
		susfs_enable_log_supercall(&arg);
		break;
	case CMD_SUSFS_ENABLE_AVC_LOG_SPOOFING:
		susfs_avc_spoof_supercall(&arg);
		break;
	case CMD_SUSFS_SET_CMDLINE_OR_BOOTCONFIG:
		susfs_spoof_cmdline_supercall(&arg);
		break;
	case CMD_SUSFS_ADD_OPEN_REDIRECT:
		susfs_open_redirect_supercall(&arg);
		break;
	case CMD_SUSFS_HIDE_SUS_MNTS_FOR_NON_SU_PROCS:
		susfs_sus_mount_supercall(&arg);
		break;
	default:

		pr_warn("susfs_guard_lkm: supercall: unsupported cmd 0x%x reached the worker (susfs_cmd_handled() and the switch disagree)\n",
			tw->cmd);
		break;
	}
	kfree(tw);
}

static bool susfs_cmd_handled(unsigned int cmd)
{
	switch (cmd) {
	case CMD_SUSFS_SHOW_VERSION:
	case CMD_SUSFS_SHOW_VARIANT:
	case CMD_SUSFS_SHOW_ENABLED_FEATURES:
	case CMD_SUSFS_ADD_SUS_PATH:
	case CMD_SUSFS_ADD_SUS_PATH_LOOP:
	case CMD_SUSFS_ADD_SUS_MAP:
	case CMD_SUSFS_ADD_SUS_KSTAT:
	case CMD_SUSFS_UPDATE_SUS_KSTAT:
	case CMD_SUSFS_ADD_SUS_KSTAT_STATICALLY:
	case CMD_SUSFS_SET_UNAME:
	case CMD_SUSFS_ENABLE_LOG:
	case CMD_SUSFS_ENABLE_AVC_LOG_SPOOFING:
	case CMD_SUSFS_SET_CMDLINE_OR_BOOTCONFIG:
	case CMD_SUSFS_ADD_OPEN_REDIRECT:
	case CMD_SUSFS_HIDE_SUS_MNTS_FOR_NON_SU_PROCS:
		return true;
	default:
		return false;
	}
}

static int reboot_pre(struct kprobe *kp, struct pt_regs *regs)
{
	struct pt_regs *real_regs = (struct pt_regs *)regs->regs[0];
	int magic1, magic2;
	unsigned int cmd;
	void __user *payload;
	struct susfs_tw *tw;

	if (!real_regs)
		return 0;

	magic1 = (int)real_regs->regs[0];
	magic2 = (int)real_regs->regs[1];
	cmd = (unsigned int)real_regs->regs[2];
	payload = (void __user *)real_regs->regs[3];

	if (magic1 != KSU_INSTALL_MAGIC1)
		return 0;
	if (magic2 != SUSFS_MAGIC)
		return 0;
	if (current_uid().val != 0)
		return 0;

	if (!susfs_cmd_handled(cmd)) {
		SUSFS_LOGI("susfs supercall: unsupported cmd 0x%x\n", cmd);
		return 0;
	}

	tw = kzalloc(sizeof(*tw), GFP_ATOMIC);
	if (!tw)
		return 0;
	tw->cmd = cmd;
	tw->payload = payload;
	tw->cb.func = susfs_tw_func;

	if (task_work_add(current, &tw->cb, TWA_RESUME)) {
		kfree(tw);
		pr_warn("susfs supercall: task_work_add failed\n");
		return 0;
	}

	regs->pc = regs->regs[30];
	regs->regs[0] = 0;
	return 1;
}

static struct kprobe reboot_kp = {
	.symbol_name = "__arm64_sys_reboot",
	.pre_handler = reboot_pre,
};

static bool sc_registered;

static void __init susfs_abi_layout_check(void)
{
	BUILD_BUG_ON(sizeof(struct st_susfs_sus_path) != 260);
	BUILD_BUG_ON(offsetof(struct st_susfs_sus_path, err) != 256);

	BUILD_BUG_ON(sizeof(struct st_susfs_sus_map) != 260);
	BUILD_BUG_ON(offsetof(struct st_susfs_sus_map, err) != 256);

	BUILD_BUG_ON(sizeof(struct st_susfs_sus_kstat) != 376);
	BUILD_BUG_ON(offsetof(struct st_susfs_sus_kstat, err) != 372);

	BUILD_BUG_ON(sizeof(struct st_susfs_uname) != 136);
	BUILD_BUG_ON(offsetof(struct st_susfs_uname, err) != 132);

	BUILD_BUG_ON(sizeof(struct st_susfs_log) != 8);
	BUILD_BUG_ON(offsetof(struct st_susfs_log, err) != 4);

	BUILD_BUG_ON(sizeof(struct st_susfs_avc_log_spoofing) != 8);
	BUILD_BUG_ON(offsetof(struct st_susfs_avc_log_spoofing, err) != 4);

	BUILD_BUG_ON(sizeof(struct st_susfs_hide_sus_mnts_for_non_su_procs) != 8);
	BUILD_BUG_ON(offsetof(struct st_susfs_hide_sus_mnts_for_non_su_procs, err) != 4);

	BUILD_BUG_ON(sizeof(struct st_susfs_open_redirect) != 520);
	BUILD_BUG_ON(offsetof(struct st_susfs_open_redirect, err) != 516);

	BUILD_BUG_ON(sizeof(struct st_susfs_spoof_cmdline_or_bootconfig) != 8196);
	BUILD_BUG_ON(offsetof(struct st_susfs_spoof_cmdline_or_bootconfig, err) != 8192);

	BUILD_BUG_ON(sizeof(struct st_susfs_version) != 20);
	BUILD_BUG_ON(offsetof(struct st_susfs_version, err) != 16);

	BUILD_BUG_ON(sizeof(struct st_susfs_variant) != 20);
	BUILD_BUG_ON(offsetof(struct st_susfs_variant, err) != 16);

	BUILD_BUG_ON(sizeof(struct st_susfs_enabled_features) != 8196);
	BUILD_BUG_ON(offsetof(struct st_susfs_enabled_features, err) != 8192);
}

int susfs_supercall_init(void)
{
	int rc;

	susfs_abi_layout_check();

	rc = register_kprobe(&reboot_kp);
	if (rc) {
		pr_warn("susfs supercall: register_kprobe(reboot) failed %d\n", rc);
		return rc;
	}
	sc_registered = true;
	SUSFS_LOGI("susfs supercall: armed (reboot ABI, version " SUSFS_VERSION_STR ")\n");
	return 0;
}

void susfs_supercall_exit(void)
{
	if (sc_registered) {
		unregister_kprobe(&reboot_kp);
		sc_registered = false;
	}
}
