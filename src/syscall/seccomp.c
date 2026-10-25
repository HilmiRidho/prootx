/* -*- c-set-style: "K&R"; c-basic-offset: 8 -*-
 *
 * This file is part of PRoot.
 *
 * Copyright (C) 2015 STMicroelectronics
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 2 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301 USA.
 */

#include "build.h"
#include "arch.h"

#if defined(HAVE_SECCOMP_FILTER)

#include <sys/prctl.h>     /* prctl(2), PR_* */
#include <linux/filter.h>  /* struct sock_*, */
#include <linux/seccomp.h> /* SECCOMP_MODE_FILTER, */
#include <linux/filter.h>  /* struct sock_*, */
#include <linux/audit.h>   /* AUDIT_, */
#include <sys/queue.h>     /* LIST_FOREACH, */
#include <sys/types.h>     /* size_t, */
#include <talloc.h>        /* talloc_*, */
#include <errno.h>         /* E*, */
#include <string.h>        /* memcpy(3), */
#include <stddef.h>        /* offsetof(3), */
#include <stdint.h>        /* uint*_t, UINT*_MAX, */
#include <assert.h>        /* assert(3), */
#include <stdlib.h>        /* qsort(3), malloc(3), free(3), */

#include "syscall/seccomp.h"
#include "tracee/tracee.h"
#include "syscall/syscall.h"
#include "syscall/sysnum.h"
#include "extension/extension.h"
#include "cli/note.h"

#include "compat.h"
#include "attribute.h"

#define DEBUG_FILTER(...) /* fprintf(stderr, __VA_ARGS__) */

/**
 * Allocate an empty @program->filter.  This function returns -errno
 * if an error occurred, otherwise 0.
 */
static int new_program_filter(struct sock_fprog *program)
{
	program->filter = talloc_array(NULL, struct sock_filter, 0);
	if (program->filter == NULL)
		return -ENOMEM;

	program->len = 0;
	return 0;
}

/**
 * Append to @program->filter the given @statements (@nb_statements
 * items).  This function returns -errno if an error occurred,
 * otherwise 0.
 */
static int add_statements(struct sock_fprog *program, size_t nb_statements,
			struct sock_filter *statements)
{
	size_t length;
	void *tmp;
	size_t i;

	length = talloc_array_length(program->filter);
	tmp  = talloc_realloc(NULL, program->filter, struct sock_filter, length + nb_statements);
	if (tmp == NULL)
		return -ENOMEM;
	program->filter = tmp;

	for (i = 0; i < nb_statements; i++, length++)
		memcpy(&program->filter[length], &statements[i], sizeof(struct sock_filter));

	return 0;
}

/* BEGIN bpf tree */

/* A filtered syscall of one architecture section.  */
typedef struct {
	uint32_t nr;	/* Architecture specific syscall number.  */
	uint32_t flags;	/* FILTER_* flags reported to the tracer.  */
	size_t order;	/* Position in the original list.  */
} TracedSyscall;

/* Sort by syscall number, then by original position, so that the first
 * occurrence of a duplicated number is the one kept (as the former
 * linear filter, which stopped at the first match).  */
static int compare_traced_syscalls(const void *a, const void *b)
{
	const TracedSyscall *x = a, *y = b;

	if (x->nr != y->nr)
		return x->nr < y->nr ? -1 : 1;
	if (x->order != y->order)
		return x->order < y->order ? -1 : 1;
	return 0;
}

/* Up to this number of syscalls, a linear chain is as fast as a
 * further dichotomy step.  */
#define LEAF_MAX 4

/**
 * Number of BPF statements emitted by emit_syscall_tree() for @n
 * syscalls.
 */
static size_t syscall_tree_length(size_t n)
{
	if (n == 0)
		return 0;

	/* JEQ+RET for each syscall, then a jump to the end of the section.  */
	if (n <= LEAF_MAX)
		return 2 * n + 1;

	/* JGE, jump over the left side, left side, right side.  */
	return 2 + syscall_tree_length(n / 2) + syscall_tree_length(n - n / 2);
}

/**
 * Write to @out the BPF statements that trace the (sorted, unique)
 * @syscalls, as a binary search tree: each syscall costs about
 * log2(n) comparisons instead of n for the former linear chain, and
 * this cost is paid on *every* syscall of every tracee, traced or not.
 * @remaining is the number of statements between the end of this tree
 * and the final "allow" statement.  This function returns the number
 * of statements written.
 */
static size_t emit_syscall_tree(struct sock_filter *out, const TracedSyscall *syscalls,
				size_t n, size_t remaining)
{
	size_t length = 0;
	size_t i;

	if (n == 0)
		return 0;

	if (n <= LEAF_MAX) {
		for (i = 0; i < n; i++) {
			/* Skip the next statement if not the expected syscall.  */
			out[length++] = (struct sock_filter) BPF_JUMP(BPF_JMP + BPF_JEQ + BPF_K,
								syscalls[i].nr, 0, 1);
			/* Notify the tracer.  */
			out[length++] = (struct sock_filter) BPF_STMT(BPF_RET + BPF_K,
								SECCOMP_RET_TRACE + syscalls[i].flags);
		}
		/* Not traced: allow.  */
		out[length++] = (struct sock_filter) BPF_STMT(BPF_JMP + BPF_JA + BPF_K, remaining);
		return length;
	}
	else {
		const size_t left_n = n / 2;
		const size_t left_length = syscall_tree_length(left_n);
		const size_t right_length = syscall_tree_length(n - left_n);

		/* Right side if syscall >= pivot (unsigned), otherwise
		 * skip the jump below and go to the left side.  */
		out[length++] = (struct sock_filter) BPF_JUMP(BPF_JMP + BPF_JGE + BPF_K,
							syscalls[left_n].nr, 0, 1);
		out[length++] = (struct sock_filter) BPF_STMT(BPF_JMP + BPF_JA + BPF_K, left_length);

		length += emit_syscall_tree(out + length, syscalls, left_n, remaining + right_length);
		length += emit_syscall_tree(out + length, syscalls + left_n, n - left_n, remaining);
		return length;
	}
}

/* END bpf tree */

/**
 * Append to @program->filter the statements that allow anything (if
 * unfiltered).  Note that @tree_length is used to make a sanity
 * check.  This function returns -errno if an error occurred,
 * otherwise 0.
 */
static int end_arch_section(struct sock_fprog *program, size_t tree_length)
{
	int status;

	#define LENGTH_END_SECTION 1
	struct sock_filter statements[LENGTH_END_SECTION] = {
		BPF_STMT(BPF_RET + BPF_K, SECCOMP_RET_ALLOW)
	};

	DEBUG_FILTER("FILTER:     allow\n");

	status = add_statements(program, LENGTH_END_SECTION, statements);
	if (status < 0)
		return status;

	/* Sanity check, see start_arch_section().  */
	if (   talloc_array_length(program->filter) - program->len
	    != LENGTH_END_SECTION + tree_length)
		return -ERANGE;

	return 0;
}

/**
 * Append to @program->filter the statements that check the current
 * @architecture.  Note that @tree_length is used to make a sanity
 * check.  This function returns -errno if an error occurred,
 * otherwise 0.
 */
static int start_arch_section(struct sock_fprog *program, uint32_t arch, size_t tree_length)
{
	const size_t arch_offset    = offsetof(struct seccomp_data, arch);
	const size_t syscall_offset = offsetof(struct seccomp_data, nr);
	const size_t section_length = LENGTH_END_SECTION + tree_length;
	int status;

	/* Sanity checks.  */
	if (   arch_offset    > UINT32_MAX
	    || syscall_offset > UINT32_MAX
	    || section_length > UINT32_MAX - 1)
		return -ERANGE;

	#define LENGTH_START_SECTION 4
	struct sock_filter statements[LENGTH_START_SECTION] = {
		/* Load the current architecture into the
		 * accumulator.  */
		BPF_STMT(BPF_LD + BPF_W + BPF_ABS, arch_offset),

		/* Compare the accumulator with the expected
		 * architecture: skip the following statement if
		 * equal.  */
		BPF_JUMP(BPF_JMP + BPF_JEQ + BPF_K, arch, 1, 0),

		/* This is not the expected architecture, so jump
		 * unconditionally to the end of this section.  */
		BPF_STMT(BPF_JMP + BPF_JA + BPF_K, section_length + 1),

		/* This is the expected architecture, so load the
		 * current syscall into the accumulator.  */
		BPF_STMT(BPF_LD + BPF_W + BPF_ABS, syscall_offset)
	};

	DEBUG_FILTER("FILTER: if arch == %ld, %zd statements\n",
		arch, tree_length);

	status = add_statements(program, LENGTH_START_SECTION, statements);
	if (status < 0)
		return status;

	/* See the sanity check in end_arch_section().  */
	program->len = talloc_array_length(program->filter);

	return 0;
}

/**
 * Append to @program->filter the statements that forbid anything (if
 * unfiltered) and update @program->len.  This function returns -errno
 * if an error occurred, otherwise 0.
 */
static int finalize_program_filter(struct sock_fprog *program)
{
	int status;

	#define LENGTH_FINALIZE 1
	struct sock_filter statements[LENGTH_FINALIZE] = {
		BPF_STMT(BPF_RET + BPF_K, SECCOMP_RET_KILL)
	};

	DEBUG_FILTER("FILTER: kill\n");

	status = add_statements(program, LENGTH_FINALIZE, statements);
	if (status < 0)
		return status;

	program->len = talloc_array_length(program->filter);

	return 0;
}

/**
 * Free @program->filter and set @program->len to 0.
 */
static void free_program_filter(struct sock_fprog *program)
{
	TALLOC_FREE(program->filter);
	program->len = 0;
}

/**
 * Convert the given @sysnums into BPF filters according to the
 * following pseudo-code, then enabled them for the given @tracee and
 * all of its future children:
 *
 *     for each handled architectures
 *         for each filtered syscall
 *             trace
 *         allow
 *     kill
 *
 * This function returns -errno if an error occurred, otherwise 0.
 */
static int set_seccomp_filters(const FilteredSysnum *sysnums)
{
	SeccompArch seccomp_archs[] = SECCOMP_ARCHS;
	size_t nb_archs = sizeof(seccomp_archs) / sizeof(SeccompArch);

	struct sock_fprog program = { .len = 0, .filter = NULL };
	TracedSyscall *traced = NULL;
	struct sock_filter *tree = NULL;
	size_t nb_traced_syscalls;
	size_t nb_unique;
	size_t tree_length;
	size_t nb_sysnums;
	size_t i, j, k;
	int status;

	status = new_program_filter(&program);
	if (status < 0)
		goto end;

	for (nb_sysnums = 0; sysnums[nb_sysnums].value != PR_void; nb_sysnums++)
		;

	/* For each handled architectures */
	for (i = 0; i < nb_archs; i++) {
		word_t syscall;

		nb_traced_syscalls = 0;

		traced = malloc((seccomp_archs[i].nb_abis * nb_sysnums + 1) * sizeof(TracedSyscall));
		if (traced == NULL) {
			status = -ENOMEM;
			goto end;
		}

		/* Collect the syscalls to trace for this architecture.  */
		for (j = 0; j < seccomp_archs[i].nb_abis; j++) {
			for (k = 0; k < nb_sysnums; k++) {
				/* Get the architecture specific syscall number.  */
				syscall = detranslate_sysnum(seccomp_archs[i].abis[j], sysnums[k].value);
				if (syscall == SYSCALL_AVOIDER)
					continue;

				/* Sanity check.  */
				if (syscall > UINT32_MAX) {
					status = -ERANGE;
					goto end;
				}

				traced[nb_traced_syscalls].nr    = (uint32_t) syscall;
				traced[nb_traced_syscalls].flags = (uint32_t) sysnums[k].flags;
				traced[nb_traced_syscalls].order = nb_traced_syscalls;
				nb_traced_syscalls++;
			}
		}

		/* Sort them and drop the duplicates, keeping the first
		 * one like the former linear filter did.  */
		qsort(traced, nb_traced_syscalls, sizeof(TracedSyscall), compare_traced_syscalls);
		for (j = 0, nb_unique = 0; j < nb_traced_syscalls; j++) {
			if (nb_unique > 0 && traced[nb_unique - 1].nr == traced[j].nr)
				continue;
			traced[nb_unique++] = traced[j];
		}

		tree_length = syscall_tree_length(nb_unique);
		tree = malloc((tree_length + 1) * sizeof(struct sock_filter));
		if (tree == NULL) {
			status = -ENOMEM;
			goto end;
		}

		if (emit_syscall_tree(tree, traced, nb_unique, 0) != tree_length) {
			status = -ERANGE;
			goto end;
		}

		/* Filter: if handled architecture */
		status = start_arch_section(&program, seccomp_archs[i].value, tree_length);
		if (status < 0)
			goto end;

		/* Filter: trace if handled syscall */
		status = add_statements(&program, tree_length, tree);
		if (status < 0)
			goto end;

		/* Filter: allow untraced syscalls for this architecture */
		status = end_arch_section(&program, tree_length);
		if (status < 0)
			goto end;

		free(tree);
		free(traced);
		tree = NULL;
		traced = NULL;
	}

	status = finalize_program_filter(&program);
	if (status < 0)
		goto end;

	status = prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0);
	if (status < 0)
		goto end;

	/* To output this BPF program for debug purpose:
	 *
	 *     write(2, program.filter, program.len * sizeof(struct sock_filter));
	 */

	status = prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, &program);
	if (status < 0)
		goto end;

	status = 0;
end:
	free(tree);
	free(traced);
	free_program_filter(&program);
	return status;
}

/* List of sysnums handled by PRoot.  */
static FilteredSysnum proot_sysnums[] = {
	{ PR_accept,		FILTER_SYSEXIT },
	{ PR_accept4,		FILTER_SYSEXIT },
	{ PR_access,		0 },
	{ PR_acct,		0 },
	{ PR_bind,		0 },
	{ PR_brk,		FILTER_SYSEXIT },
	{ PR_chdir,		FILTER_SYSEXIT },
	{ PR_chmod,		0 },
	{ PR_chown,		0 },
	{ PR_chown32,		0 },
	{ PR_chroot,		0 },
	{ PR_clone,		0 },
	{ PR_clone3,		0 },
	{ PR_close,		0 },
	{ PR_connect,		0 },
	{ PR_creat,		0 },
	{ PR_recvfrom,		0 },
	{ PR_recvmsg,		0 },
	{ PR_sendmmsg,		0 },
	{ PR_sendmsg,		0 },
	{ PR_sendto,		0 },
	{ PR_socket,		FILTER_SYSEXIT },
	{ PR_execve,		FILTER_SYSEXIT },
	{ PR_execveat,		FILTER_SYSEXIT },
	{ PR_faccessat,		0 },
	{ PR_faccessat2,	FILTER_SYSEXIT },
	{ PR_fchdir,		FILTER_SYSEXIT },
	{ PR_fchmodat,		0 },
	{ PR_fchmodat2,		0 },
	{ PR_fchownat,		0 },
	{ PR_fsconfig,		0 },
	{ PR_fsmount,		0 },
	{ PR_fsopen,		0 },
	{ PR_fspick,		0 },
	{ PR_fstatat64,		0 },
	{ PR_futimesat,		0 },
	{ PR_getcwd,		FILTER_SYSEXIT },
	{ PR_getpeername,	FILTER_SYSEXIT },
	{ PR_getsockname,	FILTER_SYSEXIT },
	{ PR_getxattr,		0 },
	{ PR_inotify_add_watch,	0 },
#ifdef __ANDROID__
	/* The exit stage is requested by the sysenter handler, only for the\n	 * few commands that need it (see PR_ioctl in syscall/enter.c).  */
	{ PR_ioctl,		0 },
#endif
	{ PR_lchown,		0 },
	{ PR_lchown32,		0 },
	{ PR_lgetxattr,		0 },
	{ PR_link,		0 },
	{ PR_linkat,		0 },
	{ PR_listxattr,		0 },
	{ PR_llistxattr,	0 },
	{ PR_lremovexattr,	0 },
	{ PR_lsetxattr,		0 },
	{ PR_lstat,		0 },
	{ PR_lstat64,		0 },
#ifdef __ANDROID__
	{ PR_memfd_create,	0 },
#endif
	{ PR_mkdir,		0 },
	{ PR_mkdirat,		0 },
	{ PR_mknod,		0 },
	{ PR_mknodat,		0 },
	{ PR_mount,		FILTER_SYSEXIT },
	{ PR_mount_setattr,	0 },
	{ PR_move_mount,	0 },
	{ PR_name_to_handle_at,	0 },
	{ PR_newfstatat,	0 },
	{ PR_oldlstat,		0 },
	{ PR_oldstat,		0 },
	{ PR_open,		0 },
	{ PR_open_tree,		0 },
	{ PR_open_tree_attr,	0 },
	{ PR_openat,		0 },
	{ PR_openat2,		0 },
	{ PR_pivot_root,	FILTER_SYSEXIT },
	{ PR_prctl, 		0 },
	{ PR_prlimit64,		FILTER_SYSEXIT },
	{ PR_ptrace,		FILTER_SYSEXIT },
	{ PR_readlink,		FILTER_SYSEXIT },
	{ PR_readlinkat,	FILTER_SYSEXIT },
	{ PR_removexattr,	0 },
	{ PR_rename,		FILTER_SYSEXIT },
	{ PR_renameat,		FILTER_SYSEXIT },
	{ PR_renameat2,		FILTER_SYSEXIT },
	{ PR_rmdir,		0 },
	{ PR_setrlimit,		FILTER_SYSEXIT },
	{ PR_setxattr,		0 },
	{ PR_socketcall,	FILTER_SYSEXIT },
	{ PR_stat,		0 },
	{ PR_stat64,		0 },
	{ PR_statfs,		FILTER_SYSEXIT },
	{ PR_statfs64,		FILTER_SYSEXIT },
	{ PR_statx,		FILTER_SYSEXIT },
	{ PR_swapoff,		0 },
	{ PR_swapon,		0 },
	{ PR_symlink,		0 },
	{ PR_symlinkat,		0 },
	{ PR_truncate,		0 },
	{ PR_truncate64,	0 },
	{ PR_umount,		FILTER_SYSEXIT },
	{ PR_umount2,		FILTER_SYSEXIT },
	{ PR_uname,		FILTER_SYSEXIT },
	{ PR_unshare,		FILTER_SYSEXIT },
	{ PR_setns,		FILTER_SYSEXIT },
	{ PR_unlink,		0 },
	{ PR_unlinkat,		0 },
	{ PR_uselib,		0 },
	{ PR_utime,		FILTER_SYSEXIT },
	{ PR_utimensat,		0 },
	{ PR_utimes,		0 },
	{ PR_wait4,		FILTER_SYSEXIT },
	{ PR_waitpid,		FILTER_SYSEXIT },
	FILTERED_SYSNUM_END,
};

/**
 * Add the @new_sysnums to the list of filtered @sysnums, using the
 * given Talloc @context.  This function returns -errno if an error
 * occurred, otherwise 0.
 */
static int merge_filtered_sysnums(TALLOC_CTX *context, FilteredSysnum **sysnums,
				const FilteredSysnum *new_sysnums)
{
	size_t i, j;

	assert(sysnums != NULL);

	if (*sysnums == NULL) {
		/* Start with no sysnums but the terminator.  */
		*sysnums = talloc_array(context, FilteredSysnum, 1);
		if (*sysnums == NULL)
			return -ENOMEM;

		(*sysnums)[0].value = PR_void;
	}

	for (i = 0; new_sysnums[i].value != PR_void; i++) {
		/* Search for the given sysnum.  */
		for (j = 0; (*sysnums)[j].value != PR_void
			 && (*sysnums)[j].value != new_sysnums[i].value; j++)
			;

		if ((*sysnums)[j].value == PR_void) {
			/* No such sysnum, allocate a new entry.  */
			(*sysnums) = talloc_realloc(context, (*sysnums), FilteredSysnum, j + 2);
			if ((*sysnums) == NULL)
				return -ENOMEM;

			(*sysnums)[j] = new_sysnums[i];

			/* The last item is the terminator.  */
			(*sysnums)[j + 1].value = PR_void;
		}
		else
			/* The sysnum is already filtered, merge the
			 * flags.  */
			(*sysnums)[j].flags |= new_sysnums[i].flags;
	}

	return 0;
}

/**
 * Tell the kernel to trace only syscalls handled by PRoot and its
 * extensions.  This filter will be enabled for the given @tracee and
 * all of its future children.  This function returns -errno if an
 * error occurred, otherwise 0.
 */
int enable_syscall_filtering(const Tracee *tracee)
{
	FilteredSysnum *filtered_sysnums = NULL;
	Extension *extension;
	int status;

	assert(tracee != NULL && tracee->ctx != NULL);

	/* Add the sysnums required by PRoot to the list of filtered
	 * sysnums.  TODO: only if path translation is required.  */
	status = merge_filtered_sysnums(tracee->ctx, &filtered_sysnums, proot_sysnums);
	if (status < 0)
		return status;

	/* Merge the sysnums required by the extensions to the list
	 * of filtered sysnums.  */
	if (tracee->extensions != NULL) {
		LIST_FOREACH(extension, tracee->extensions, link) {
			if (extension->filtered_sysnums == NULL)
				continue;

			status = merge_filtered_sysnums(tracee->ctx, &filtered_sysnums,
							extension->filtered_sysnums);
			if (status < 0)
				return status;
		}
	}

	status = set_seccomp_filters(filtered_sysnums);
	if (status < 0)
		return status;

	return 0;
}

/**
 * Return the flags the filter of enable_syscall_filtering() associates
 * with @sysnum for @tracee, ie. the data PTRACE_EVENT_SECCOMP stops of
 * that syscall report: the filter was built from the very same lists.
 */
int filtered_sysnum_flags(const Tracee *tracee, Sysnum sysnum)
{
	Extension *extension;
	int flags = 0;
	size_t i;

	for (i = 0; proot_sysnums[i].value != PR_void; i++) {
		if (proot_sysnums[i].value == sysnum)
			flags |= proot_sysnums[i].flags;
	}

	if (tracee->extensions == NULL)
		return flags;

	LIST_FOREACH(extension, tracee->extensions, link) {
		if (extension->filtered_sysnums == NULL)
			continue;

		for (i = 0; extension->filtered_sysnums[i].value != PR_void; i++) {
			if (extension->filtered_sysnums[i].value == sysnum)
				flags |= extension->filtered_sysnums[i].flags;
		}
	}

	return flags;
}

#else

#include "syscall/seccomp.h"
#include "tracee/tracee.h"
#include "attribute.h"

int enable_syscall_filtering(const Tracee *tracee UNUSED)
{
	return 0;
}

int filtered_sysnum_flags(const Tracee *tracee UNUSED, Sysnum sysnum UNUSED)
{
	return 0;
}

#endif /* defined(HAVE_SECCOMP_FILTER) */
