// SPDX-License-Identifier: GPL-2.0-or-later
/*
 *  fs/eventpoll.c (Efficient event retrieval implementation)
 *  Copyright (C) 2001,...,2009	 Davide Libenzi
 *
 *  Davide Libenzi <davidel@xmailserver.org>
 */

#include <linux/init.h>
#include <linux/kernel.h>
#include <linux/sched/signal.h>
#include <linux/fs.h>
#include <linux/file.h>
#include <linux/signal.h>
#include <linux/errno.h>
#include <linux/mm.h>
#include <linux/slab.h>
#include <linux/poll.h>
#include <linux/string.h>
#include <linux/list.h>
#include <linux/hash.h>
#include <linux/spinlock.h>
#include <linux/syscalls.h>
#include <linux/rbtree.h>
#include <linux/wait.h>
#include <linux/eventpoll.h>
#include <linux/mount.h>
#include <linux/bitops.h>
#include <linux/mutex.h>
#include <linux/anon_inodes.h>
#include <linux/device.h>
#include <linux/uaccess.h>
#include <asm/io.h>
#include <asm/mman.h>
#include <linux/atomic.h>
#include <linux/proc_fs.h>
#include <linux/seq_file.h>
#include <linux/compat.h>
#include <linux/rculist.h>
#include <linux/capability.h>
#include <net/busy_poll.h>

/*
 * LOCKING:
 * There are three level of locking required by epoll :
 * epoll 需要三个级别的锁定
 *
 * 1) epnested_mutex (mutex)
 * 2) ep->mtx (mutex)
 * 3) ep->lock (rwlock)
 *
 * The acquire order is the one listed above, from 1 to 3.
 * We need a rwlock (ep->lock) because we manipulate objects
 * from inside the poll callback, that might be triggered from
 * a wake_up() that in turn might be called from IRQ context.
 * So we can't sleep inside the poll callback and hence we need
 * a spinlock. During the event transfer loop (from kernel to
 * user space) we could end up sleeping due a copy_to_user(), so
 * we need a lock that will allow us to sleep. This lock is a
 * mutex (ep->mtx). It is acquired during the event transfer loop,
 * during epoll_ctl(EPOLL_CTL_DEL) and during eventpoll_release_file().
 * The epnested_mutex is acquired when inserting an epoll fd onto another
 * epoll fd. We do this so that we walk the epoll tree and ensure that this
 * insertion does not create a cycle of epoll file descriptors, which
 * could lead to deadlock. We need a global mutex to prevent two
 * simultaneous inserts (A into B and B into A) from racing and
 * constructing a cycle without either insert observing that it is
 * going to.
 * 获取的顺序是上面列出的顺序，从1到3.
 * 我们需要一个 rwlock 锁，因为我们从轮询回调内部操作对象，这可能是由 wake_up() 触发的，而 wake_up 又可能是从 IRQ 上下文中调用。
 * 所以我们不能在轮询回调中睡眠，因此我们需要一个自旋锁。在事件传输循环期间（从内核到用户空间），我们可能因为 copy_to_user() 结束睡眠，所以我们需要一把能让我们睡眠的锁。
 * 这个锁是 mutex(ep->mtx)。它是在事件传递循环期间获得的，在 epoll_ctl 和 eventpoll_release_file()。
 * epnested_mutex 是在插入epoll fd到另一个 epoll fd 时获取的。这样做是为了遍历 epoll 树，并确保插入不会创建 epoll 文件描述符的循环，这可能导致死锁。
 * 我们需要一个全局互斥锁来防止两个同时插入（a插入到b，b插入到a），在没有一个插入观察到它将要进行的情况向下竞争并构造一个循环
 *
 * It is necessary to acquire multiple "ep->mtx"es at once in the
 * case when one epoll fd is added to another. In this case, we
 * always acquire the locks in the order of nesting (i.e. after
 * epoll_ctl(e1, EPOLL_CTL_ADD, e2), e1->mtx will always be acquired
 * before e2->mtx). Since we disallow cycles of epoll file
 * descriptors, this ensures that the mutexes are well-ordered. In
 * order to communicate this nesting to lockdep, when walking a tree
 * of epoll file descriptors, we use the current recursion depth as
 * the lockdep subkey.
 * 当一个 epoll fd 添加到另一个 epoll fd时，需要一次获取多个 ep->mtx。
 * 在这个场景下，我们总是按照嵌套的顺序获取锁（即在 epoll_ctl(e1, EPOLL_CTL_ADD, e2)之后，e1->mtx 总是在 e2->mtx 之前获得）。
 * 由于我们不允许 epoll 文件描述符的循环，这确保了互斥锁是有序的。
 * 为了将这种嵌套传递给 lockdep，在遍历 epoll 文件描述符树时，我们使用当前递归深度作为 lockdep 子键。
 *
 * It is possible to drop the "ep->mtx" and to use the global
 * mutex "epnested_mutex" (together with "ep->lock") to have it working,
 * but having "ep->mtx" will make the interface more scalable.
 * Events that require holding "epnested_mutex" are very rare, while for
 * normal operations the epoll private "ep->mtx" will guarantee
 * a better scalability.
 * 可以删除 ep->mtx 并使用全局互斥锁 epnested_mutex(连同 ep->lock) 使其工作，但是 ep->mtx 将使界面更具可扩展性。
 * 需要持有 epnested_mutex 的事件非常罕见，而对于正常操作， epoll 私有 ep->mtx 将保证更好的可伸缩性。
 *
 */

/* Epoll private bits inside the event mask */
#define EP_PRIVATE_BITS (EPOLLWAKEUP | EPOLLONESHOT | EPOLLET | EPOLLEXCLUSIVE)

#define EPOLLINOUT_BITS (EPOLLIN | EPOLLOUT)

#define EPOLLEXCLUSIVE_OK_BITS (EPOLLINOUT_BITS | EPOLLERR | EPOLLHUP | \
				EPOLLWAKEUP | EPOLLET | EPOLLEXCLUSIVE)

/* Maximum number of nesting allowed inside epoll sets */
#define EP_MAX_NESTS 4

#define EP_MAX_EVENTS (INT_MAX / sizeof(struct epoll_event))

#define EP_UNACTIVE_PTR ((void *) -1L)

#define EP_ITEM_COST (sizeof(struct epitem) + sizeof(struct eppoll_entry))

struct epoll_filefd {
	struct file *file;
	int fd;
} __packed;

/* Wait structure used by the poll hooks
 * poll 钩子使用的等待结构
 * */
struct eppoll_entry {
	/* List header used to link this structure to the "struct epitem"
	 * 用于将该结构体链接到 struct epitem 的列表头
	 * */
	struct eppoll_entry *next;

	/* The "base" pointer is set to the container "struct epitem"
	 * base指针指向容器 struct epitem
	 * */
	struct epitem *base;

	/*
	 * Wait queue item that will be linked to the target file wait
	 * queue head.
	 * 将链接到目标文件等待队列头的等待队列项
	 */
	wait_queue_entry_t wait;

	/* The wait queue head that linked the "wait" wait queue item
	 * 链接 wait 等待队列项的等待队列头
	 * */
	wait_queue_head_t *whead;
};

/*
 * Each file descriptor added to the eventpoll interface will
 * have an entry of this type linked to the "rbr" RB tree.
 * Avoid increasing the size of this struct, there can be many thousands
 * of these on a server and we do not want this to take another cache line.
 * 添加到 eventpoll 接口的每个文件描述符都有一个链接到 rbr RB 树的这种类型的条目。
 * 避免增加该结构体的大小，服务器上可能有数千个这样的结构体，我们不希望它占用另一条缓存线
 */
struct epitem {
	union {
		/* RB tree node links this structure to the eventpoll RB tree
		 * RB树节点将此结构链接到 eventpoll RB树
		 * */
		struct rb_node rbn;
		/* Used to free the struct epitem
		 * 用于释放结构体 epitem
		 * */
		struct rcu_head rcu;
	};

	/* List header used to link this structure to the eventpoll ready list
	 * 列表头用于将此结构链接到 eventpoll 就绪列表
	 * */
	struct list_head rdllink;

	/*
	 * Works together "struct eventpoll"->ovflist in keeping the
	 * single linked chain of items.
	 * 同 "struct eventpoll"->ovflist 一起工作，保持单项链接
	 */
	struct epitem *next;

	/* The file descriptor information this item refers to
	 * 该项所引用的文件描述符信息
	 * */
	struct epoll_filefd ffd;

	/*
	 * Protected by file->f_lock, true for to-be-released epitem already
	 * removed from the "struct file" items list; together with
	 * eventpoll->refcount orchestrates "struct eventpoll" disposal
	 * 受 file->f_lock 保护，对于即将释放的 epitem 已经从 struct file 项列表中删除，为true
	 * 与 eventpoll->refcount 一起编排了 struct eventpoll 的处理
	 */
	bool dying;

	/* List containing poll wait queues
	 * 包含轮询等待队列的列表
	 * */
	struct eppoll_entry *pwqlist;

	/* The "container" of this item
	 * 该项目的容器
	 * */
	struct eventpoll *ep;

	/* List header used to link this item to the "struct file" items list
	 * 列表头文件，用于将该项链接到 struct file 的项列表
	 * */
	struct hlist_node fllink;

	/* wakeup_source used when EPOLLWAKEUP is set
	 * wakeup_source 在 EPOLLWAKEUP 被设置时使用
	 * */
	struct wakeup_source __rcu *ws;

	/* The structure that describe the interested events and the source fd
	 * 描述感兴趣的事件和源fd的结构
	 * */
	struct epoll_event event;
};

/*
 * This structure is stored inside the "private_data" member of the file
 * structure and represents the main data structure for the eventpoll
 * interface.
 * 这个结构存储在文件结构的 private_data 成员中，代表 eventpoll 接口的主要数据结构
 */
struct eventpoll {
	/*
	 * This mutex is used to ensure that files are not removed
	 * while epoll is using them. This is held during the event
	 * collection loop, the file cleanup path, the epoll file exit
	 * code and the ctl operations.
	 * 这个互斥锁用于确保 epoll 使用文件时文件不会被删除。这在事件收集循环，文件清理路径，epoll文件退出代码和 ctl 操作期间进行
	 */
	struct mutex mtx;

	/* Wait queue used by sys_epoll_wait()
	 * sys_epoll_wait 使用的等待队列
	 * */
	wait_queue_head_t wq;

	/* Wait queue used by file->poll()
	 *  file->poll()使用的等待队列
	 * */
	wait_queue_head_t poll_wait;

	/* List of ready file descriptors
	 * 已就绪文件描述符的列表
	 * */
	struct list_head rdllist;

	/* Lock which protects rdllist and ovflist
	 * 保护 rdllist 和 ovflist 的锁
	 * */
	rwlock_t lock;

	/* RB tree root used to store monitored fd structs
	 * RB树的根用来存储受监控的 fd 结构
	 * */
	struct rb_root_cached rbr;

	/*
	 * This is a single linked list that chains all the "struct epitem" that
	 * happened while transferring ready events to userspace w/out
	 * holding ->lock.
	 * 这是一个链表，它将所有在将就绪时间转移到用户空间时发生的 struct epitem 链接到一起，并持有锁
	 */
	struct epitem *ovflist;

	/* wakeup_source used when ep_send_events or __ep_eventpoll_poll is running
	 * 当 ep_send_events 或 __ep_eventpoll_poll 在运行时使用 wakeup_source
	 * */
	struct wakeup_source *ws;

	/* The user that created the eventpoll descriptor
	 * 创建 eventpoll 描述符的用户
	 * */
	struct user_struct *user;

	// 文件
	struct file *file;

	/* used to optimize loop detection check
	 * 用于优化环路检测
	 * */
	u64 gen;
	struct hlist_head refs;

	/*
	 * usage count, used together with epitem->dying to
	 * orchestrate the disposal of this struct
	 * 使用计数，与 epitem->dying 一起使用，以编排该结构的位置
	 */
	refcount_t refcount;

#ifdef CONFIG_NET_RX_BUSY_POLL
	/* used to track busy poll napi_id */
	unsigned int napi_id;
	/* busy poll timeout */
	u32 busy_poll_usecs;
	/* busy poll packet budget */
	u16 busy_poll_budget;
	bool prefer_busy_poll;
#endif

#ifdef CONFIG_DEBUG_LOCK_ALLOC
	/* tracks wakeup nests for lockdep validation */
	u8 nests;
#endif
};

/* Wrapper struct used by poll queueing
 * 轮询队列使用的包装器结构
 * */
struct ep_pqueue {
	poll_table pt;
	struct epitem *epi;
};

/*
 * Configuration options available inside /proc/sys/fs/epoll/
 */
/* Maximum number of epoll watched descriptors, per user */
static long max_user_watches __read_mostly;

/* Used for cycles detection */
static DEFINE_MUTEX(epnested_mutex);

static u64 loop_check_gen = 0;

/* Used to check for epoll file descriptor inclusion loops */
static struct eventpoll *inserting_into;

/* Slab cache used to allocate "struct epitem" */
static struct kmem_cache *epi_cache __ro_after_init;

/* Slab cache used to allocate "struct eppoll_entry" */
static struct kmem_cache *pwq_cache __ro_after_init;

/*
 * List of files with newly added links, where we may need to limit the number
 * of emanating paths. Protected by the epnested_mutex.
 */
struct epitems_head {
	struct hlist_head epitems;
	struct epitems_head *next;
};
static struct epitems_head *tfile_check_list = EP_UNACTIVE_PTR;

static struct kmem_cache *ephead_cache __ro_after_init;

static inline void free_ephead(struct epitems_head *head)
{
	if (head)
		kmem_cache_free(ephead_cache, head);
}

static void list_file(struct file *file)
{
	struct epitems_head *head;

	head = container_of(file->f_ep, struct epitems_head, epitems);
	if (!head->next) {
		head->next = tfile_check_list;
		tfile_check_list = head;
	}
}

static void unlist_file(struct epitems_head *head)
{
	struct epitems_head *to_free = head;
	struct hlist_node *p = rcu_dereference(hlist_first_rcu(&head->epitems));
	if (p) {
		struct epitem *epi= container_of(p, struct epitem, fllink);
		spin_lock(&epi->ffd.file->f_lock);
		if (!hlist_empty(&head->epitems))
			to_free = NULL;
		head->next = NULL;
		spin_unlock(&epi->ffd.file->f_lock);
	}
	free_ephead(to_free);
}

#ifdef CONFIG_SYSCTL

#include <linux/sysctl.h>

static long long_zero;
static long long_max = LONG_MAX;

static const struct ctl_table epoll_table[] = {
	{
		.procname	= "max_user_watches",
		.data		= &max_user_watches,
		.maxlen		= sizeof(max_user_watches),
		.mode		= 0644,
		.proc_handler	= proc_doulongvec_minmax,
		.extra1		= &long_zero,
		.extra2		= &long_max,
	},
};

static void __init epoll_sysctls_init(void)
{
	register_sysctl("fs/epoll", epoll_table);
}
#else
#define epoll_sysctls_init() do { } while (0)
#endif /* CONFIG_SYSCTL */

static const struct file_operations eventpoll_fops;

static inline int is_file_epoll(struct file *f)
{
	return f->f_op == &eventpoll_fops;
}

/* Setup the structure that is used as key for the RB tree */
static inline void ep_set_ffd(struct epoll_filefd *ffd,
			      struct file *file, int fd)
{
	ffd->file = file;
	ffd->fd = fd;
}

/* Compare RB tree keys */
static inline int ep_cmp_ffd(struct epoll_filefd *p1,
			     struct epoll_filefd *p2)
{
	return (p1->file > p2->file ? +1:
	        (p1->file < p2->file ? -1 : p1->fd - p2->fd));
}

/* Tells us if the item is currently linked */
static inline int ep_is_linked(struct epitem *epi)
{
	return !list_empty(&epi->rdllink);
}

static inline struct eppoll_entry *ep_pwq_from_wait(wait_queue_entry_t *p)
{
	return container_of(p, struct eppoll_entry, wait);
}

/* Get the "struct epitem" from a wait queue pointer */
static inline struct epitem *ep_item_from_wait(wait_queue_entry_t *p)
{
	return container_of(p, struct eppoll_entry, wait)->base;
}

/**
 * ep_events_available - Checks if ready events might be available.
 * 检查事件是否有效
 *
 * @ep: Pointer to the eventpoll context.
 *
 * Return: a value different than %zero if ready events are available,
 *          or %zero otherwise.
 */
static inline int ep_events_available(struct eventpoll *ep)
{
	return !list_empty_careful(&ep->rdllist) ||
		READ_ONCE(ep->ovflist) != EP_UNACTIVE_PTR;
}

#ifdef CONFIG_NET_RX_BUSY_POLL
/**
 * busy_loop_ep_timeout - check if busy poll has timed out. The timeout value
 * from the epoll instance ep is preferred, but if it is not set fallback to
 * the system-wide global via busy_loop_timeout.
 *
 * @start_time: The start time used to compute the remaining time until timeout.
 * @ep: Pointer to the eventpoll context.
 *
 * Return: true if the timeout has expired, false otherwise.
 */
static bool busy_loop_ep_timeout(unsigned long start_time,
				 struct eventpoll *ep)
{
	unsigned long bp_usec = READ_ONCE(ep->busy_poll_usecs);

	if (bp_usec) {
		unsigned long end_time = start_time + bp_usec;
		unsigned long now = busy_loop_current_time();

		return time_after(now, end_time);
	} else {
		return busy_loop_timeout(start_time);
	}
}

static bool ep_busy_loop_on(struct eventpoll *ep)
{
	return !!READ_ONCE(ep->busy_poll_usecs) ||
	       READ_ONCE(ep->prefer_busy_poll) ||
	       net_busy_loop_on();
}

static bool ep_busy_loop_end(void *p, unsigned long start_time)
{
	struct eventpoll *ep = p;

	return ep_events_available(ep) || busy_loop_ep_timeout(start_time, ep);
}

/*
 * Busy poll if globally on and supporting sockets found && no events,
 * busy loop will return if need_resched or ep_events_available.
 *
 * we must do our busy polling with irqs enabled
 */
static bool ep_busy_loop(struct eventpoll *ep)
{
	unsigned int napi_id = READ_ONCE(ep->napi_id);
	u16 budget = READ_ONCE(ep->busy_poll_budget);
	bool prefer_busy_poll = READ_ONCE(ep->prefer_busy_poll);

	if (!budget)
		budget = BUSY_POLL_BUDGET;

	if (napi_id_valid(napi_id) && ep_busy_loop_on(ep)) {
		napi_busy_loop(napi_id, ep_busy_loop_end,
			       ep, prefer_busy_poll, budget);
		if (ep_events_available(ep))
			return true;
		/*
		 * Busy poll timed out.  Drop NAPI ID for now, we can add
		 * it back in when we have moved a socket with a valid NAPI
		 * ID onto the ready list.
		 */
		if (prefer_busy_poll)
			napi_resume_irqs(napi_id);
		ep->napi_id = 0;
		return false;
	}
	return false;
}

/*
 * Set epoll busy poll NAPI ID from sk.
 */
static inline void ep_set_busy_poll_napi_id(struct epitem *epi)
{
	struct eventpoll *ep = epi->ep;
	unsigned int napi_id;
	struct socket *sock;
	struct sock *sk;

	if (!ep_busy_loop_on(ep))
		return;

	sock = sock_from_file(epi->ffd.file);
	if (!sock)
		return;

	sk = sock->sk;
	if (!sk)
		return;

	napi_id = READ_ONCE(sk->sk_napi_id);

	/* Non-NAPI IDs can be rejected
	 *	or
	 * Nothing to do if we already have this ID
	 */
	if (!napi_id_valid(napi_id) || napi_id == ep->napi_id)
		return;

	/* record NAPI ID for use in next busy poll */
	ep->napi_id = napi_id;
}

static long ep_eventpoll_bp_ioctl(struct file *file, unsigned int cmd,
				  unsigned long arg)
{
	struct eventpoll *ep = file->private_data;
	void __user *uarg = (void __user *)arg;
	struct epoll_params epoll_params;

	switch (cmd) {
	case EPIOCSPARAMS:
		if (copy_from_user(&epoll_params, uarg, sizeof(epoll_params)))
			return -EFAULT;

		/* pad byte must be zero */
		if (epoll_params.__pad)
			return -EINVAL;

		if (epoll_params.busy_poll_usecs > S32_MAX)
			return -EINVAL;

		if (epoll_params.prefer_busy_poll > 1)
			return -EINVAL;

		if (epoll_params.busy_poll_budget > NAPI_POLL_WEIGHT &&
		    !capable(CAP_NET_ADMIN))
			return -EPERM;

		WRITE_ONCE(ep->busy_poll_usecs, epoll_params.busy_poll_usecs);
		WRITE_ONCE(ep->busy_poll_budget, epoll_params.busy_poll_budget);
		WRITE_ONCE(ep->prefer_busy_poll, epoll_params.prefer_busy_poll);
		return 0;
	case EPIOCGPARAMS:
		memset(&epoll_params, 0, sizeof(epoll_params));
		epoll_params.busy_poll_usecs = READ_ONCE(ep->busy_poll_usecs);
		epoll_params.busy_poll_budget = READ_ONCE(ep->busy_poll_budget);
		epoll_params.prefer_busy_poll = READ_ONCE(ep->prefer_busy_poll);
		if (copy_to_user(uarg, &epoll_params, sizeof(epoll_params)))
			return -EFAULT;
		return 0;
	default:
		return -ENOIOCTLCMD;
	}
}

static void ep_suspend_napi_irqs(struct eventpoll *ep)
{
	unsigned int napi_id = READ_ONCE(ep->napi_id);

	if (napi_id_valid(napi_id) && READ_ONCE(ep->prefer_busy_poll))
		napi_suspend_irqs(napi_id);
}

static void ep_resume_napi_irqs(struct eventpoll *ep)
{
	unsigned int napi_id = READ_ONCE(ep->napi_id);

	if (napi_id_valid(napi_id) && READ_ONCE(ep->prefer_busy_poll))
		napi_resume_irqs(napi_id);
}

#else

static inline bool ep_busy_loop(struct eventpoll *ep)
{
	return false;
}

static inline void ep_set_busy_poll_napi_id(struct epitem *epi)
{
}

static long ep_eventpoll_bp_ioctl(struct file *file, unsigned int cmd,
				  unsigned long arg)
{
	return -EOPNOTSUPP;
}

static void ep_suspend_napi_irqs(struct eventpoll *ep)
{
}

static void ep_resume_napi_irqs(struct eventpoll *ep)
{
}

#endif /* CONFIG_NET_RX_BUSY_POLL */

/*
 * As described in commit 0ccf831cb lockdep: annotate epoll
 * the use of wait queues used by epoll is done in a very controlled
 * manner. Wake ups can nest inside each other, but are never done
 * with the same locking. For example:
 *
 *   dfd = socket(...);
 *   efd1 = epoll_create();
 *   efd2 = epoll_create();
 *   epoll_ctl(efd1, EPOLL_CTL_ADD, dfd, ...);
 *   epoll_ctl(efd2, EPOLL_CTL_ADD, efd1, ...);
 *
 * When a packet arrives to the device underneath "dfd", the net code will
 * issue a wake_up() on its poll wake list. Epoll (efd1) has installed a
 * callback wakeup entry on that queue, and the wake_up() performed by the
 * "dfd" net code will end up in ep_poll_callback(). At this point epoll
 * (efd1) notices that it may have some event ready, so it needs to wake up
 * the waiters on its poll wait list (efd2). So it calls ep_poll_safewake()
 * that ends up in another wake_up(), after having checked about the
 * recursion constraints. That are, no more than EP_MAX_NESTS, to avoid
 * stack blasting.
 *
 * When CONFIG_DEBUG_LOCK_ALLOC is enabled, make sure lockdep can handle
 * this special case of epoll.
 */
#ifdef CONFIG_DEBUG_LOCK_ALLOC

static void ep_poll_safewake(struct eventpoll *ep, struct epitem *epi,
			     unsigned pollflags)
{
	struct eventpoll *ep_src;
	unsigned long flags;
	u8 nests = 0;

	/*
	 * To set the subclass or nesting level for spin_lock_irqsave_nested()
	 * it might be natural to create a per-cpu nest count. However, since
	 * we can recurse on ep->poll_wait.lock, and a non-raw spinlock can
	 * schedule() in the -rt kernel, the per-cpu variable are no longer
	 * protected. Thus, we are introducing a per eventpoll nest field.
	 * If we are not being call from ep_poll_callback(), epi is NULL and
	 * we are at the first level of nesting, 0. Otherwise, we are being
	 * called from ep_poll_callback() and if a previous wakeup source is
	 * not an epoll file itself, we are at depth 1 since the wakeup source
	 * is depth 0. If the wakeup source is a previous epoll file in the
	 * wakeup chain then we use its nests value and record ours as
	 * nests + 1. The previous epoll file nests value is stable since its
	 * already holding its own poll_wait.lock.
	 */
	if (epi) {
		if ((is_file_epoll(epi->ffd.file))) {
			ep_src = epi->ffd.file->private_data;
			nests = ep_src->nests;
		} else {
			nests = 1;
		}
	}
	spin_lock_irqsave_nested(&ep->poll_wait.lock, flags, nests);
	ep->nests = nests + 1;
	wake_up_locked_poll(&ep->poll_wait, EPOLLIN | pollflags);
	ep->nests = 0;
	spin_unlock_irqrestore(&ep->poll_wait.lock, flags);
}

#else

static void ep_poll_safewake(struct eventpoll *ep, struct epitem *epi,
			     __poll_t pollflags)
{
	wake_up_poll(&ep->poll_wait, EPOLLIN | pollflags);
}

#endif

static void ep_remove_wait_queue(struct eppoll_entry *pwq)
{
	wait_queue_head_t *whead;

	rcu_read_lock();
	/*
	 * If it is cleared by POLLFREE, it should be rcu-safe.
	 * If we read NULL we need a barrier paired with
	 * smp_store_release() in ep_poll_callback(), otherwise
	 * we rely on whead->lock.
	 */
	whead = smp_load_acquire(&pwq->whead);
	if (whead)
		remove_wait_queue(whead, &pwq->wait);
	rcu_read_unlock();
}

/*
 * This function unregisters poll callbacks from the associated file
 * descriptor.  Must be called with "mtx" held.
 */
static void ep_unregister_pollwait(struct eventpoll *ep, struct epitem *epi)
{
	struct eppoll_entry **p = &epi->pwqlist;
	struct eppoll_entry *pwq;

	while ((pwq = *p) != NULL) {
		*p = pwq->next;
		ep_remove_wait_queue(pwq);
		kmem_cache_free(pwq_cache, pwq);
	}
}

/* call only when ep->mtx is held */
static inline struct wakeup_source *ep_wakeup_source(struct epitem *epi)
{
	return rcu_dereference_check(epi->ws, lockdep_is_held(&epi->ep->mtx));
}

/* call only when ep->mtx is held */
static inline void ep_pm_stay_awake(struct epitem *epi)
{
	struct wakeup_source *ws = ep_wakeup_source(epi);

	if (ws)
		__pm_stay_awake(ws);
}

static inline bool ep_has_wakeup_source(struct epitem *epi)
{
	return rcu_access_pointer(epi->ws) ? true : false;
}

/* call when ep->mtx cannot be held (ep_poll_callback) */
static inline void ep_pm_stay_awake_rcu(struct epitem *epi)
{
	struct wakeup_source *ws;

	rcu_read_lock();
	ws = rcu_dereference(epi->ws);
	if (ws)
		__pm_stay_awake(ws);
	rcu_read_unlock();
}


/*
 * ep->mutex needs to be held because we could be hit by
 * eventpoll_release_file() and epoll_ctl().
 */
static void ep_start_scan(struct eventpoll *ep, struct list_head *txlist)
{
	/*
	 * Steal the ready list, and re-init the original one to the
	 * empty list. Also, set ep->ovflist to NULL so that events
	 * happening while looping w/out locks, are not lost. We cannot
	 * have the poll callback to queue directly on ep->rdllist,
	 * because we want the "sproc" callback to be able to do it
	 * in a lockless way.
	 */
	lockdep_assert_irqs_enabled();
	write_lock_irq(&ep->lock);
	list_splice_init(&ep->rdllist, txlist);
	WRITE_ONCE(ep->ovflist, NULL);
	write_unlock_irq(&ep->lock);
}

static void ep_done_scan(struct eventpoll *ep,
			 struct list_head *txlist)
{
	struct epitem *epi, *nepi;

	write_lock_irq(&ep->lock);
	/*
	 * During the time we spent inside the "sproc" callback, some
	 * other events might have been queued by the poll callback.
	 * We re-insert them inside the main ready-list here.
	 */
	for (nepi = READ_ONCE(ep->ovflist); (epi = nepi) != NULL;
	     nepi = epi->next, epi->next = EP_UNACTIVE_PTR) {
		/*
		 * We need to check if the item is already in the list.
		 * During the "sproc" callback execution time, items are
		 * queued into ->ovflist but the "txlist" might already
		 * contain them, and the list_splice() below takes care of them.
		 */
		if (!ep_is_linked(epi)) {
			/*
			 * ->ovflist is LIFO, so we have to reverse it in order
			 * to keep in FIFO.
			 */
			list_add(&epi->rdllink, &ep->rdllist);
			ep_pm_stay_awake(epi);
		}
	}
	/*
	 * We need to set back ep->ovflist to EP_UNACTIVE_PTR, so that after
	 * releasing the lock, events will be queued in the normal way inside
	 * ep->rdllist.
	 */
	WRITE_ONCE(ep->ovflist, EP_UNACTIVE_PTR);

	/*
	 * Quickly re-inject items left on "txlist".
	 */
	list_splice(txlist, &ep->rdllist);
	__pm_relax(ep->ws);

	if (!list_empty(&ep->rdllist)) {
		if (waitqueue_active(&ep->wq))
			wake_up(&ep->wq);
	}

	write_unlock_irq(&ep->lock);
}

static void ep_get(struct eventpoll *ep)
{
	refcount_inc(&ep->refcount);
}

/*
 * Returns true if the event poll can be disposed
 */
static bool ep_refcount_dec_and_test(struct eventpoll *ep)
{
	if (!refcount_dec_and_test(&ep->refcount))
		return false;

	WARN_ON_ONCE(!RB_EMPTY_ROOT(&ep->rbr.rb_root));
	return true;
}

static void ep_free(struct eventpoll *ep)
{
	ep_resume_napi_irqs(ep);
	mutex_destroy(&ep->mtx);
	free_uid(ep->user);
	wakeup_source_unregister(ep->ws);
	kfree(ep);
}

/*
 * Removes a "struct epitem" from the eventpoll RB tree and deallocates
 * all the associated resources. Must be called with "mtx" held.
 * If the dying flag is set, do the removal only if force is true.
 * This prevents ep_clear_and_put() from dropping all the ep references
 * while running concurrently with eventpoll_release_file().
 * Returns true if the eventpoll can be disposed.
 */
static bool __ep_remove(struct eventpoll *ep, struct epitem *epi, bool force)
{
	struct file *file = epi->ffd.file;
	struct epitems_head *to_free;
	struct hlist_head *head;

	lockdep_assert_irqs_enabled();

	/*
	 * Removes poll wait queue hooks.
	 */
	ep_unregister_pollwait(ep, epi);

	/* Remove the current item from the list of epoll hooks */
	spin_lock(&file->f_lock);
	if (epi->dying && !force) {
		spin_unlock(&file->f_lock);
		return false;
	}

	to_free = NULL;
	head = file->f_ep;
	if (head->first == &epi->fllink && !epi->fllink.next) {
		/* See eventpoll_release() for details. */
		WRITE_ONCE(file->f_ep, NULL);
		if (!is_file_epoll(file)) {
			struct epitems_head *v;
			v = container_of(head, struct epitems_head, epitems);
			if (!smp_load_acquire(&v->next))
				to_free = v;
		}
	}
	hlist_del_rcu(&epi->fllink);
	spin_unlock(&file->f_lock);
	free_ephead(to_free);

	rb_erase_cached(&epi->rbn, &ep->rbr);

	write_lock_irq(&ep->lock);
	if (ep_is_linked(epi))
		list_del_init(&epi->rdllink);
	write_unlock_irq(&ep->lock);

	wakeup_source_unregister(ep_wakeup_source(epi));
	/*
	 * At this point it is safe to free the eventpoll item. Use the union
	 * field epi->rcu, since we are trying to minimize the size of
	 * 'struct epitem'. The 'rbn' field is no longer in use. Protected by
	 * ep->mtx. The rcu read side, reverse_path_check_proc(), does not make
	 * use of the rbn field.
	 */
	kfree_rcu(epi, rcu);

	percpu_counter_dec(&ep->user->epoll_watches);
	return ep_refcount_dec_and_test(ep);
}

/*
 * ep_remove variant for callers owing an additional reference to the ep
 */
static void ep_remove_safe(struct eventpoll *ep, struct epitem *epi)
{
	WARN_ON_ONCE(__ep_remove(ep, epi, false));
}

static void ep_clear_and_put(struct eventpoll *ep)
{
	struct rb_node *rbp, *next;
	struct epitem *epi;
	bool dispose;

	/* We need to release all tasks waiting for these file */
	if (waitqueue_active(&ep->poll_wait))
		ep_poll_safewake(ep, NULL, 0);

	mutex_lock(&ep->mtx);

	/*
	 * Walks through the whole tree by unregistering poll callbacks.
	 */
	for (rbp = rb_first_cached(&ep->rbr); rbp; rbp = rb_next(rbp)) {
		epi = rb_entry(rbp, struct epitem, rbn);

		ep_unregister_pollwait(ep, epi);
		cond_resched();
	}

	/*
	 * Walks through the whole tree and try to free each "struct epitem".
	 * Note that ep_remove_safe() will not remove the epitem in case of a
	 * racing eventpoll_release_file(); the latter will do the removal.
	 * At this point we are sure no poll callbacks will be lingering around.
	 * Since we still own a reference to the eventpoll struct, the loop can't
	 * dispose it.
	 */
	for (rbp = rb_first_cached(&ep->rbr); rbp; rbp = next) {
		next = rb_next(rbp);
		epi = rb_entry(rbp, struct epitem, rbn);
		ep_remove_safe(ep, epi);
		cond_resched();
	}

	dispose = ep_refcount_dec_and_test(ep);
	mutex_unlock(&ep->mtx);

	if (dispose)
		ep_free(ep);
}

static long ep_eventpoll_ioctl(struct file *file, unsigned int cmd,
			       unsigned long arg)
{
	int ret;

	if (!is_file_epoll(file))
		return -EINVAL;

	switch (cmd) {
	case EPIOCSPARAMS:
	case EPIOCGPARAMS:
		ret = ep_eventpoll_bp_ioctl(file, cmd, arg);
		break;
	default:
		ret = -EINVAL;
		break;
	}

	return ret;
}

static int ep_eventpoll_release(struct inode *inode, struct file *file)
{
	struct eventpoll *ep = file->private_data;

	if (ep)
		ep_clear_and_put(ep);

	return 0;
}

static __poll_t ep_item_poll(const struct epitem *epi, poll_table *pt, int depth);

static __poll_t __ep_eventpoll_poll(struct file *file, poll_table *wait, int depth)
{
	struct eventpoll *ep = file->private_data;
	LIST_HEAD(txlist);
	struct epitem *epi, *tmp;
	poll_table pt;
	__poll_t res = 0;

	init_poll_funcptr(&pt, NULL);

	/* Insert inside our poll wait queue */
	poll_wait(file, &ep->poll_wait, wait);

	/*
	 * Proceed to find out if wanted events are really available inside
	 * the ready list.
	 */
	mutex_lock_nested(&ep->mtx, depth);
	ep_start_scan(ep, &txlist);
	list_for_each_entry_safe(epi, tmp, &txlist, rdllink) {
		if (ep_item_poll(epi, &pt, depth + 1)) {
			res = EPOLLIN | EPOLLRDNORM;
			break;
		} else {
			/*
			 * Item has been dropped into the ready list by the poll
			 * callback, but it's not actually ready, as far as
			 * caller requested events goes. We can remove it here.
			 */
			__pm_relax(ep_wakeup_source(epi));
			list_del_init(&epi->rdllink);
		}
	}
	ep_done_scan(ep, &txlist);
	mutex_unlock(&ep->mtx);
	return res;
}

/*
 * The ffd.file pointer may be in the process of being torn down due to
 * being closed, but we may not have finished eventpoll_release() yet.
 *
 * Normally, even with the atomic_long_inc_not_zero, the file may have
 * been free'd and then gotten re-allocated to something else (since
 * files are not RCU-delayed, they are SLAB_TYPESAFE_BY_RCU).
 *
 * But for epoll, users hold the ep->mtx mutex, and as such any file in
 * the process of being free'd will block in eventpoll_release_file()
 * and thus the underlying file allocation will not be free'd, and the
 * file re-use cannot happen.
 *
 * For the same reason we can avoid a rcu_read_lock() around the
 * operation - 'ffd.file' cannot go away even if the refcount has
 * reached zero (but we must still not call out to ->poll() functions
 * etc).
 */
static struct file *epi_fget(const struct epitem *epi)
{
	struct file *file;

	file = epi->ffd.file;
	if (!file_ref_get(&file->f_ref))
		file = NULL;
	return file;
}

/*
 * Differs from ep_eventpoll_poll() in that internal callers already have
 * the ep->mtx so we need to start from depth=1, such that mutex_lock_nested()
 * is correctly annotated.
 * 与ep_eventpoll_poll的不同之处在于，内部调用者已经拥有 ep-mtx 因此我们需要从 depth=1开始，这样 mutex_lock_nested 才能被正确注释
 */
static __poll_t ep_item_poll(const struct epitem *epi, poll_table *pt,
				 int depth)
{
	struct file *file = epi_fget(epi);
	__poll_t res;

	/*
	 * We could return EPOLLERR | EPOLLHUP or something, but let's
	 * treat this more as "file doesn't exist, poll didn't happen".
	 */
	if (!file)
		return 0;

	pt->_key = epi->event.events;
	if (!is_file_epoll(file))
		res = vfs_poll(file, pt);
	else
		res = __ep_eventpoll_poll(file, pt, depth);
	fput(file);
	return res & epi->event.events;
}

static __poll_t ep_eventpoll_poll(struct file *file, poll_table *wait)
{
	return __ep_eventpoll_poll(file, wait, 0);
}

#ifdef CONFIG_PROC_FS
static void ep_show_fdinfo(struct seq_file *m, struct file *f)
{
	struct eventpoll *ep = f->private_data;
	struct rb_node *rbp;

	mutex_lock(&ep->mtx);
	for (rbp = rb_first_cached(&ep->rbr); rbp; rbp = rb_next(rbp)) {
		struct epitem *epi = rb_entry(rbp, struct epitem, rbn);
		struct inode *inode = file_inode(epi->ffd.file);

		seq_printf(m, "tfd: %8d events: %8x data: %16llx "
			   " pos:%lli ino:%lx sdev:%x\n",
			   epi->ffd.fd, epi->event.events,
			   (long long)epi->event.data,
			   (long long)epi->ffd.file->f_pos,
			   inode->i_ino, inode->i_sb->s_dev);
		if (seq_has_overflowed(m))
			break;
	}
	mutex_unlock(&ep->mtx);
}
#endif

/* File callbacks that implement the eventpoll file behaviour */
static const struct file_operations eventpoll_fops = {
#ifdef CONFIG_PROC_FS
	.show_fdinfo	= ep_show_fdinfo,
#endif
	.release	= ep_eventpoll_release,
	.poll		= ep_eventpoll_poll,
	.llseek		= noop_llseek,
	.unlocked_ioctl	= ep_eventpoll_ioctl,
	.compat_ioctl   = compat_ptr_ioctl,
};

/*
 * This is called from eventpoll_release() to unlink files from the eventpoll
 * interface. We need to have this facility to cleanup correctly files that are
 * closed without being removed from the eventpoll interface.
 */
void eventpoll_release_file(struct file *file)
{
	struct eventpoll *ep;
	struct epitem *epi;
	bool dispose;

	/*
	 * Use the 'dying' flag to prevent a concurrent ep_clear_and_put() from
	 * touching the epitems list before eventpoll_release_file() can access
	 * the ep->mtx.
	 */
again:
	spin_lock(&file->f_lock);
	if (file->f_ep && file->f_ep->first) {
		epi = hlist_entry(file->f_ep->first, struct epitem, fllink);
		epi->dying = true;
		spin_unlock(&file->f_lock);

		/*
		 * ep access is safe as we still own a reference to the ep
		 * struct
		 */
		ep = epi->ep;
		mutex_lock(&ep->mtx);
		dispose = __ep_remove(ep, epi, true);
		mutex_unlock(&ep->mtx);

		if (dispose)
			ep_free(ep);
		goto again;
	}
	spin_unlock(&file->f_lock);
}

static int ep_alloc(struct eventpoll **pep)
{
	//初始化 epoll 属性
	struct eventpoll *ep;

	ep = kzalloc(sizeof(*ep), GFP_KERNEL);
	if (unlikely(!ep))
		return -ENOMEM;

	mutex_init(&ep->mtx);
	rwlock_init(&ep->lock);
	init_waitqueue_head(&ep->wq);
	init_waitqueue_head(&ep->poll_wait);
	INIT_LIST_HEAD(&ep->rdllist);
	ep->rbr = RB_ROOT_CACHED;
	ep->ovflist = EP_UNACTIVE_PTR;
	ep->user = get_current_user();
	refcount_set(&ep->refcount, 1);

	*pep = ep;

	return 0;
}

/*
 * Search the file inside the eventpoll tree. The RB tree operations
 * are protected by the "mtx" mutex, and ep_find() must be called with
 * "mtx" held.
 * 从 eventpoll 树中查找文件。 RB 树操作被 mtx 互斥保护，并且 ep_find 被调用时必须持有 mtx
 *
 */
static struct epitem *ep_find(struct eventpoll *ep, struct file *file, int fd)
{
	int kcmp;
	struct rb_node *rbp;
	struct epitem *epi, *epir = NULL;
	struct epoll_filefd ffd;

	ep_set_ffd(&ffd, file, fd);
	for (rbp = ep->rbr.rb_root.rb_node; rbp; ) {
		//找到当前节点
		epi = rb_entry(rbp, struct epitem, rbn);
		//比较大小
		kcmp = ep_cmp_ffd(&ffd, &epi->ffd);
		//若大于则继续指向右节点
		if (kcmp > 0)
			rbp = rbp->rb_right;
		else if (kcmp < 0)//若小于则继续指向左节点
			rbp = rbp->rb_left;
		else {//相等则直接返回
			epir = epi;
			break;
		}
	}

	return epir;
}

#ifdef CONFIG_KCMP
static struct epitem *ep_find_tfd(struct eventpoll *ep, int tfd, unsigned long toff)
{
	struct rb_node *rbp;
	struct epitem *epi;

	for (rbp = rb_first_cached(&ep->rbr); rbp; rbp = rb_next(rbp)) {
		epi = rb_entry(rbp, struct epitem, rbn);
		if (epi->ffd.fd == tfd) {
			if (toff == 0)
				return epi;
			else
				toff--;
		}
		cond_resched();
	}

	return NULL;
}

struct file *get_epoll_tfile_raw_ptr(struct file *file, int tfd,
				     unsigned long toff)
{
	struct file *file_raw;
	struct eventpoll *ep;
	struct epitem *epi;

	if (!is_file_epoll(file))
		return ERR_PTR(-EINVAL);

	ep = file->private_data;

	mutex_lock(&ep->mtx);
	epi = ep_find_tfd(ep, tfd, toff);
	if (epi)
		file_raw = epi->ffd.file;
	else
		file_raw = ERR_PTR(-ENOENT);
	mutex_unlock(&ep->mtx);

	return file_raw;
}
#endif /* CONFIG_KCMP */

/*
 * Adds a new entry to the tail of the list in a lockless way, i.e.
 * multiple CPUs are allowed to call this function concurrently.
 *
 * Beware: it is necessary to prevent any other modifications of the
 *         existing list until all changes are completed, in other words
 *         concurrent list_add_tail_lockless() calls should be protected
 *         with a read lock, where write lock acts as a barrier which
 *         makes sure all list_add_tail_lockless() calls are fully
 *         completed.
 *
 *        Also an element can be locklessly added to the list only in one
 *        direction i.e. either to the tail or to the head, otherwise
 *        concurrent access will corrupt the list.
 *
 * Return: %false if element has been already added to the list, %true
 * otherwise.
 */
static inline bool list_add_tail_lockless(struct list_head *new,
					  struct list_head *head)
{
	struct list_head *prev;

	/*
	 * This is simple 'new->next = head' operation, but cmpxchg()
	 * is used in order to detect that same element has been just
	 * added to the list from another CPU: the winner observes
	 * new->next == new.
	 */
	if (!try_cmpxchg(&new->next, &new, head))
		return false;

	/*
	 * Initially ->next of a new element must be updated with the head
	 * (we are inserting to the tail) and only then pointers are atomically
	 * exchanged.  XCHG guarantees memory ordering, thus ->next should be
	 * updated before pointers are actually swapped and pointers are
	 * swapped before prev->next is updated.
	 */

	prev = xchg(&head->prev, new);

	/*
	 * It is safe to modify prev->next and new->prev, because a new element
	 * is added only to the tail and new->next is updated before XCHG.
	 */

	prev->next = new;
	new->prev = prev;

	return true;
}

/*
 * Chains a new epi entry to the tail of the ep->ovflist in a lockless way,
 * i.e. multiple CPUs are allowed to call this function concurrently.
 *
 * Return: %false if epi element has been already chained, %true otherwise.
 */
static inline bool chain_epi_lockless(struct epitem *epi)
{
	struct eventpoll *ep = epi->ep;

	/* Fast preliminary check */
	if (epi->next != EP_UNACTIVE_PTR)
		return false;

	/* Check that the same epi has not been just chained from another CPU */
	if (cmpxchg(&epi->next, EP_UNACTIVE_PTR, NULL) != EP_UNACTIVE_PTR)
		return false;

	/* Atomically exchange tail */
	epi->next = xchg(&ep->ovflist, epi);

	return true;
}

/*
 * This is the callback that is passed to the wait queue wakeup
 * mechanism. It is called by the stored file descriptors when they
 * have events to report.
 * 这是传递给等待队列唤醒机制的回调。存储的文件描述符在需要报告事件时调用它
 *
 * This callback takes a read lock in order not to contend with concurrent
 * events from another file descriptor, thus all modifications to ->rdllist
 * or ->ovflist are lockless.  Read lock is paired with the write lock from
 * ep_start/done_scan(), which stops all list modifications and guarantees
 * that lists state is seen correctly.
 * 为了不与来自另一个文件描述符的并发事件竞争，这个回调使用了一个读锁。因此对 rdllist 或 ovflist的所有修改都是无锁的。
 * 读锁 与来自 ep_start/done_scan 的写锁配对，它停止所有列表修改并保证列表状态被正确看到
 *
 * Another thing worth to mention is that ep_poll_callback() can be called
 * concurrently for the same @epi from different CPUs if poll table was inited
 * with several wait queues entries.  Plural wakeup from different CPUs of a
 * single wait queue is serialized by wq.lock, but the case when multiple wait
 * queues are used should be detected accordingly.  This is detected using
 * cmpxchg() operation.
 * 另一件值得提及 的事情是，如果轮询表是用多个等待队列项发起的，那么可以从不同的cpu并发的为同一个 epi 调用 ep_poll_callback 。
 * wq对单个等待队列中不同的cpu的多个唤醒进行序列化。锁，但是应该相应的检测使用多个等待队列的情况。这是使用 cmxchg 操作检测的，
 */
static int ep_poll_callback(wait_queue_entry_t *wait, unsigned mode, int sync, void *key)
{
	int pwake = 0;
	struct epitem *epi = ep_item_from_wait(wait);
	struct eventpoll *ep = epi->ep;
	__poll_t pollflags = key_to_poll(key);
	unsigned long flags;
	int ewake = 0;

	read_lock_irqsave(&ep->lock, flags);

	ep_set_busy_poll_napi_id(epi);

	/*
	 * If the event mask does not contain any poll(2) event, we consider the
	 * descriptor to be disabled. This condition is likely the effect of the
	 * EPOLLONESHOT bit that disables the descriptor when an event is received,
	 * until the next EPOLL_CTL_MOD will be issued.
	 */
	if (!(epi->event.events & ~EP_PRIVATE_BITS))
		goto out_unlock;

	/*
	 * Check the events coming with the callback. At this stage, not
	 * every device reports the events in the "key" parameter of the
	 * callback. We need to be able to handle both cases here, hence the
	 * test for "key" != NULL before the event match test.
	 */
	if (pollflags && !(pollflags & epi->event.events))
		goto out_unlock;

	/*
	 * If we are transferring events to userspace, we can hold no locks
	 * (because we're accessing user memory, and because of linux f_op->poll()
	 * semantics). All the events that happen during that period of time are
	 * chained in ep->ovflist and requeued later on.
	 */
	if (READ_ONCE(ep->ovflist) != EP_UNACTIVE_PTR) {
		if (chain_epi_lockless(epi))
			ep_pm_stay_awake_rcu(epi);
	} else if (!ep_is_linked(epi)) {
		/* In the usual case, add event to ready list. */
		if (list_add_tail_lockless(&epi->rdllink, &ep->rdllist))
			ep_pm_stay_awake_rcu(epi);
	}

	/*
	 * Wake up ( if active ) both the eventpoll wait list and the ->poll()
	 * wait list.
	 */
	if (waitqueue_active(&ep->wq)) {
		if ((epi->event.events & EPOLLEXCLUSIVE) &&
					!(pollflags & POLLFREE)) {
			switch (pollflags & EPOLLINOUT_BITS) {
			case EPOLLIN:
				if (epi->event.events & EPOLLIN)
					ewake = 1;
				break;
			case EPOLLOUT:
				if (epi->event.events & EPOLLOUT)
					ewake = 1;
				break;
			case 0:
				ewake = 1;
				break;
			}
		}
		if (sync)
			wake_up_sync(&ep->wq);
		else
			wake_up(&ep->wq);
	}
	if (waitqueue_active(&ep->poll_wait))
		pwake++;

out_unlock:
	read_unlock_irqrestore(&ep->lock, flags);

	/* We have to call this outside the lock */
	if (pwake)
		ep_poll_safewake(ep, epi, pollflags & EPOLL_URING_WAKE);

	if (!(epi->event.events & EPOLLEXCLUSIVE))
		ewake = 1;

	if (pollflags & POLLFREE) {
		/*
		 * If we race with ep_remove_wait_queue() it can miss
		 * ->whead = NULL and do another remove_wait_queue() after
		 * us, so we can't use __remove_wait_queue().
		 */
		list_del_init(&wait->entry);
		/*
		 * ->whead != NULL protects us from the race with
		 * ep_clear_and_put() or ep_remove(), ep_remove_wait_queue()
		 * takes whead->lock held by the caller. Once we nullify it,
		 * nothing protects ep/epi or even wait.
		 */
		smp_store_release(&ep_pwq_from_wait(wait)->whead, NULL);
	}

	return ewake;
}

/*
 * This is the callback that is used to add our wait queue to the
 * target file wakeup lists.
 * 这个回调函数用于将等待队列添加到目标文件唤醒列表中
 *
 */
static void ep_ptable_queue_proc(struct file *file, wait_queue_head_t *whead,
				 poll_table *pt)
{
	struct ep_pqueue *epq = container_of(pt, struct ep_pqueue, pt);
	struct epitem *epi = epq->epi;
	struct eppoll_entry *pwq;

	if (unlikely(!epi))	// an earlier allocation has failed
		return;

	pwq = kmem_cache_alloc(pwq_cache, GFP_KERNEL);
	if (unlikely(!pwq)) {
		epq->epi = NULL;
		return;
	}

	//将ep_poll_callback初始化为等待队列中的方法调用
	init_waitqueue_func_entry(&pwq->wait, ep_poll_callback);
	pwq->whead = whead;
	pwq->base = epi;
	if (epi->event.events & EPOLLEXCLUSIVE)
		add_wait_queue_exclusive(whead, &pwq->wait);
	else
		add_wait_queue(whead, &pwq->wait);
	pwq->next = epi->pwqlist;
	epi->pwqlist = pwq;
}

static void ep_rbtree_insert(struct eventpoll *ep, struct epitem *epi)
{
	int kcmp;
	struct rb_node **p = &ep->rbr.rb_root.rb_node, *parent = NULL;
	struct epitem *epic;
	bool leftmost = true;

	//从根节点开始寻找  比较待插入文件的大小 找到插入位置及父节点
	while (*p) {
		parent = *p;
		epic = rb_entry(parent, struct epitem, rbn);
		kcmp = ep_cmp_ffd(&epi->ffd, &epic->ffd);
		if (kcmp > 0) {
			p = &parent->rb_right;
			leftmost = false;
		} else
			p = &parent->rb_left;
	}
	//插入节点
	rb_link_node(&epi->rbn, parent, p);
	//节点染色
	rb_insert_color_cached(&epi->rbn, &ep->rbr, leftmost);
}



#define PATH_ARR_SIZE 5
/*
 * These are the number paths of length 1 to 5, that we are allowing to emanate
 * from a single file of interest. For example, we allow 1000 paths of length
 * 1, to emanate from each file of interest. This essentially represents the
 * potential wakeup paths, which need to be limited in order to avoid massive
 * uncontrolled wakeup storms. The common use case should be a single ep which
 * is connected to n file sources. In this case each file source has 1 path
 * of length 1. Thus, the numbers below should be more than sufficient. These
 * path limits are enforced during an EPOLL_CTL_ADD operation, since a modify
 * and delete can't add additional paths. Protected by the epnested_mutex.
 */
static const int path_limits[PATH_ARR_SIZE] = { 1000, 500, 100, 50, 10 };
static int path_count[PATH_ARR_SIZE];

static int path_count_inc(int nests)
{
	/* Allow an arbitrary number of depth 1 paths */
	if (nests == 0)
		return 0;

	if (++path_count[nests] > path_limits[nests])
		return -1;
	return 0;
}

static void path_count_init(void)
{
	int i;

	for (i = 0; i < PATH_ARR_SIZE; i++)
		path_count[i] = 0;
}

static int reverse_path_check_proc(struct hlist_head *refs, int depth)
{
	int error = 0;
	struct epitem *epi;

	if (depth > EP_MAX_NESTS) /* too deep nesting */
		return -1;

	/* CTL_DEL can remove links here, but that can't increase our count */
	hlist_for_each_entry_rcu(epi, refs, fllink) {
		struct hlist_head *refs = &epi->ep->refs;
		if (hlist_empty(refs))
			error = path_count_inc(depth);
		else
			error = reverse_path_check_proc(refs, depth + 1);
		if (error != 0)
			break;
	}
	return error;
}

/**
 * reverse_path_check - The tfile_check_list is list of epitem_head, which have
 *                      links that are proposed to be newly added. We need to
 *                      make sure that those added links don't add too many
 *                      paths such that we will spend all our time waking up
 *                      eventpoll objects.
 *
 * Return: %zero if the proposed links don't create too many paths,
 *	    %-1 otherwise.
 */
static int reverse_path_check(void)
{
	struct epitems_head *p;

	for (p = tfile_check_list; p != EP_UNACTIVE_PTR; p = p->next) {
		int error;
		path_count_init();
		rcu_read_lock();
		error = reverse_path_check_proc(&p->epitems, 0);
		rcu_read_unlock();
		if (error)
			return error;
	}
	return 0;
}

static int ep_create_wakeup_source(struct epitem *epi)
{
	struct name_snapshot n;
	struct wakeup_source *ws;

	if (!epi->ep->ws) {
		epi->ep->ws = wakeup_source_register(NULL, "eventpoll");
		if (!epi->ep->ws)
			return -ENOMEM;
	}

	take_dentry_name_snapshot(&n, epi->ffd.file->f_path.dentry);
	ws = wakeup_source_register(NULL, n.name.name);
	release_dentry_name_snapshot(&n);

	if (!ws)
		return -ENOMEM;
	rcu_assign_pointer(epi->ws, ws);

	return 0;
}

/* rare code path, only used when EPOLL_CTL_MOD removes a wakeup source */
static noinline void ep_destroy_wakeup_source(struct epitem *epi)
{
	struct wakeup_source *ws = ep_wakeup_source(epi);

	RCU_INIT_POINTER(epi->ws, NULL);

	/*
	 * wait for ep_pm_stay_awake_rcu to finish, synchronize_rcu is
	 * used internally by wakeup_source_remove, too (called by
	 * wakeup_source_unregister), so we cannot use call_rcu
	 */
	synchronize_rcu();
	wakeup_source_unregister(ws);
}

static int attach_epitem(struct file *file, struct epitem *epi)
{
	struct epitems_head *to_free = NULL;
	struct hlist_head *head = NULL;
	struct eventpoll *ep = NULL;

	if (is_file_epoll(file))
		ep = file->private_data;

	if (ep) {
		head = &ep->refs;
	} else if (!READ_ONCE(file->f_ep)) {
allocate:
		to_free = kmem_cache_zalloc(ephead_cache, GFP_KERNEL);
		if (!to_free)
			return -ENOMEM;
		head = &to_free->epitems;
	}
	spin_lock(&file->f_lock);
	if (!file->f_ep) {
		if (unlikely(!head)) {
			spin_unlock(&file->f_lock);
			goto allocate;
		}
		/* See eventpoll_release() for details. */
		WRITE_ONCE(file->f_ep, head);
		to_free = NULL;
	}
	hlist_add_head_rcu(&epi->fllink, file->f_ep);
	spin_unlock(&file->f_lock);
	free_ephead(to_free);
	return 0;
}

/*
 * Must be called with "mtx" held.
 * 调用时必须有 mtx
 */
static int ep_insert(struct eventpoll *ep, const struct epoll_event *event,
		     struct file *tfile, int fd, int full_check)
{
	int error, pwake = 0;
	__poll_t revents;
	struct epitem *epi;
	struct ep_pqueue epq;
	struct eventpoll *tep = NULL;

	//判断是否 epoll 文件
	if (is_file_epoll(tfile))
		//获取文件中 eventpoll
		tep = tfile->private_data;

	lockdep_assert_irqs_enabled();

	//判断是否超过可支持用户的最大限制
	if (unlikely(percpu_counter_compare(&ep->user->epoll_watches,
					    max_user_watches) >= 0))
		return -ENOSPC;
	//用户计数加1
	percpu_counter_inc(&ep->user->epoll_watches);

	//分配 epi内存 若分配失败则计数减1
	if (!(epi = kmem_cache_zalloc(epi_cache, GFP_KERNEL))) {
		percpu_counter_dec(&ep->user->epoll_watches);
		return -ENOMEM;
	}

	/* Item initialization follow here ...
	 * 以下都是item初始化
	 * */
	//初始化就绪列表
	INIT_LIST_HEAD(&epi->rdllink);
	//ep 指向 eventpoll
	epi->ep = ep;
	//将用户文件 指向 epi中的ffd
	ep_set_ffd(&epi->ffd, tfile, fd);
	//初始化事件
	epi->event = *event;
	epi->next = EP_UNACTIVE_PTR;

	if (tep)
		mutex_lock_nested(&tep->mtx, 1);
	/* Add the current item to the list of active epoll hook for this file
	 * 将当前项添加到该文件的活动epoll钩子列表中
	 * */
	if (unlikely(attach_epitem(tfile, epi) < 0)) {
		if (tep)
			mutex_unlock(&tep->mtx);
		kmem_cache_free(epi_cache, epi);
		percpu_counter_dec(&ep->user->epoll_watches);
		return -ENOMEM;
	}

	if (full_check && !tep)
		list_file(tfile);

	/*
	 * Add the current item to the RB tree. All RB tree operations are
	 * protected by "mtx", and ep_insert() is called with "mtx" held.
	 * 将此item添加到RB树中。所有的RB树操作都被 mtx 保护，ep_insert 调用时必须持有 mtx
	 */
	ep_rbtree_insert(ep, epi);
	if (tep)
		mutex_unlock(&tep->mtx);

	/*
	 * ep_remove_safe() calls in the later error paths can't lead to
	 * ep_free() as the ep file itself still holds an ep reference.
	 * 后面的错误路径中的 ep_remove_safe() 调用不能导致 ep_free()，因为 ep文件本身仍然持有一个 ep 引用
	 */
	ep_get(ep);

	/* now check if we've created too many backpaths
	 * 现在检查我们是否创建了太多的回路
	 * */
	if (unlikely(full_check && reverse_path_check())) {
		ep_remove_safe(ep, epi);
		return -EINVAL;
	}

	if (epi->event.events & EPOLLWAKEUP) {
		error = ep_create_wakeup_source(epi);
		if (error) {
			ep_remove_safe(ep, epi);
			return error;
		}
	}

	/* Initialize the poll table using the queue callback
	 * 使用队列回调初始化轮询表
	 * */
	epq.epi = epi;
	//初始化等待队列 即 ep_poll_callback
	init_poll_funcptr(&epq.pt, ep_ptable_queue_proc);

	/*
	 * Attach the item to the poll hooks and get current event bits.
	 * We can safely use the file* here because its usage count has
	 * been increased by the caller of this function. Note that after
	 * this operation completes, the poll callback can start hitting
	 * the new item.
	 * 将项目附加到轮询挂载并获取当前事件位。
	 * 我们可以安全的在这里使用这个文件，因为它的使用计数已经被这个函数的调用者增加了。
	 * 注意 在此操作完成后，轮询回调可以开始命中新项
	 */
	revents = ep_item_poll(epi, &epq.pt, 1);

	/*
	 * We have to check if something went wrong during the poll wait queue
	 * install process. Namely an allocation for a wait queue failed due
	 * high memory pressure.
	 * 我们必须检查在轮询等待队列安装过程中是否出现了问题。也就是说，由于内存压力大，等待队列的分配失败
	 */
	if (unlikely(!epq.epi)) {
		ep_remove_safe(ep, epi);
		return -ENOMEM;
	}

	/* We have to drop the new item inside our item list to keep track of it
	 * 我们必须将新项目放入项目列表中以跟踪它
	 * */
	write_lock_irq(&ep->lock);

	/* record NAPI ID of new item if present */
	ep_set_busy_poll_napi_id(epi);

	/* If the file is already "ready" we drop it inside the ready list */
	if (revents && !ep_is_linked(epi)) {
		list_add_tail(&epi->rdllink, &ep->rdllist);
		ep_pm_stay_awake(epi);

		/* Notify waiting tasks that events are available */
		if (waitqueue_active(&ep->wq))
			wake_up(&ep->wq);
		if (waitqueue_active(&ep->poll_wait))
			pwake++;
	}

	write_unlock_irq(&ep->lock);

	/* We have to call this outside the lock */
	if (pwake)
		ep_poll_safewake(ep, NULL, 0);

	return 0;
}

/*
 * Modify the interest event mask by dropping an event if the new mask
 * has a match in the current file status. Must be called with "mtx" held.
 */
static int ep_modify(struct eventpoll *ep, struct epitem *epi,
		     const struct epoll_event *event)
{
	int pwake = 0;
	poll_table pt;

	lockdep_assert_irqs_enabled();

	init_poll_funcptr(&pt, NULL);

	/*
	 * Set the new event interest mask before calling f_op->poll();
	 * otherwise we might miss an event that happens between the
	 * f_op->poll() call and the new event set registering.
	 */
	epi->event.events = event->events; /* need barrier below */
	epi->event.data = event->data; /* protected by mtx */
	if (epi->event.events & EPOLLWAKEUP) {
		if (!ep_has_wakeup_source(epi))
			ep_create_wakeup_source(epi);
	} else if (ep_has_wakeup_source(epi)) {
		ep_destroy_wakeup_source(epi);
	}

	/*
	 * The following barrier has two effects:
	 *
	 * 1) Flush epi changes above to other CPUs.  This ensures
	 *    we do not miss events from ep_poll_callback if an
	 *    event occurs immediately after we call f_op->poll().
	 *    We need this because we did not take ep->lock while
	 *    changing epi above (but ep_poll_callback does take
	 *    ep->lock).
	 *
	 * 2) We also need to ensure we do not miss _past_ events
	 *    when calling f_op->poll().  This barrier also
	 *    pairs with the barrier in wq_has_sleeper (see
	 *    comments for wq_has_sleeper).
	 *
	 * This barrier will now guarantee ep_poll_callback or f_op->poll
	 * (or both) will notice the readiness of an item.
	 */
	smp_mb();

	/*
	 * Get current event bits. We can safely use the file* here because
	 * its usage count has been increased by the caller of this function.
	 * If the item is "hot" and it is not registered inside the ready
	 * list, push it inside.
	 */
	if (ep_item_poll(epi, &pt, 1)) {
		write_lock_irq(&ep->lock);
		if (!ep_is_linked(epi)) {
			list_add_tail(&epi->rdllink, &ep->rdllist);
			ep_pm_stay_awake(epi);

			/* Notify waiting tasks that events are available */
			if (waitqueue_active(&ep->wq))
				wake_up(&ep->wq);
			if (waitqueue_active(&ep->poll_wait))
				pwake++;
		}
		write_unlock_irq(&ep->lock);
	}

	/* We have to call this outside the lock */
	if (pwake)
		ep_poll_safewake(ep, NULL, 0);

	return 0;
}

static int ep_send_events(struct eventpoll *ep,
			  struct epoll_event __user *events, int maxevents)
{
	struct epitem *epi, *tmp;
	LIST_HEAD(txlist);
	poll_table pt;
	int res = 0;

	/*
	 * Always short-circuit for fatal signals to allow threads to make a
	 * timely exit without the chance of finding more events available and
	 * fetching repeatedly.
	 */
	if (fatal_signal_pending(current))
		return -EINTR;

	init_poll_funcptr(&pt, NULL);

	mutex_lock(&ep->mtx);
	ep_start_scan(ep, &txlist);

	/*
	 * We can loop without lock because we are passed a task private list.
	 * Items cannot vanish during the loop we are holding ep->mtx.
	 */
	list_for_each_entry_safe(epi, tmp, &txlist, rdllink) {
		struct wakeup_source *ws;
		__poll_t revents;

		if (res >= maxevents)
			break;

		/*
		 * Activate ep->ws before deactivating epi->ws to prevent
		 * triggering auto-suspend here (in case we reactive epi->ws
		 * below).
		 *
		 * This could be rearranged to delay the deactivation of epi->ws
		 * instead, but then epi->ws would temporarily be out of sync
		 * with ep_is_linked().
		 */
		ws = ep_wakeup_source(epi);
		if (ws) {
			if (ws->active)
				__pm_stay_awake(ep->ws);
			__pm_relax(ws);
		}

		list_del_init(&epi->rdllink);

		/*
		 * If the event mask intersect the caller-requested one,
		 * deliver the event to userspace. Again, we are holding ep->mtx,
		 * so no operations coming from userspace can change the item.
		 */
		revents = ep_item_poll(epi, &pt, 1);
		if (!revents)
			continue;

		events = epoll_put_uevent(revents, epi->event.data, events);
		if (!events) {
			list_add(&epi->rdllink, &txlist);
			ep_pm_stay_awake(epi);
			if (!res)
				res = -EFAULT;
			break;
		}
		res++;
		if (epi->event.events & EPOLLONESHOT)
			epi->event.events &= EP_PRIVATE_BITS;
		else if (!(epi->event.events & EPOLLET)) {
			/*
			 * If this file has been added with Level
			 * Trigger mode, we need to insert back inside
			 * the ready list, so that the next call to
			 * epoll_wait() will check again the events
			 * availability. At this point, no one can insert
			 * into ep->rdllist besides us. The epoll_ctl()
			 * callers are locked out by
			 * ep_send_events() holding "mtx" and the
			 * poll callback will queue them in ep->ovflist.
			 */
			list_add_tail(&epi->rdllink, &ep->rdllist);
			ep_pm_stay_awake(epi);
		}
	}
	ep_done_scan(ep, &txlist);
	mutex_unlock(&ep->mtx);

	return res;
}

static struct timespec64 *ep_timeout_to_timespec(struct timespec64 *to, long ms)
{
	struct timespec64 now;

	if (ms < 0)
		return NULL;

	if (!ms) {
		to->tv_sec = 0;
		to->tv_nsec = 0;
		return to;
	}

	to->tv_sec = ms / MSEC_PER_SEC;
	to->tv_nsec = NSEC_PER_MSEC * (ms % MSEC_PER_SEC);

	ktime_get_ts64(&now);
	*to = timespec64_add_safe(now, *to);
	return to;
}

/*
 * autoremove_wake_function, but remove even on failure to wake up, because we
 * know that default_wake_function/ttwu will only fail if the thread is already
 * woken, and in that case the ep_poll loop will remove the entry anyways, not
 * try to reuse it.
 * autoremove_wake_function 但即使在唤醒失败时也要删除，因为我们知道  default_wake_function/ttwu 只会在线程已经被唤醒时失败，在这种情况下， ep_poll 循环无论如何都会删除条目，而不是尝试重用它
 */
static int ep_autoremove_wake_function(struct wait_queue_entry *wq_entry,
				       unsigned int mode, int sync, void *key)
{
	int ret = default_wake_function(wq_entry, mode, sync, key);

	/*
	 * Pairs with list_empty_careful in ep_poll, and ensures future loop
	 * iterations see the cause of this wakeup.
	 */
	list_del_init_careful(&wq_entry->entry);
	return ret;
}

static int ep_try_send_events(struct eventpoll *ep,
			      struct epoll_event __user *events, int maxevents)
{
	int res;

	/*
	 * Try to transfer events to user space. In case we get 0 events and
	 * there's still timeout left over, we go trying again in search of
	 * more luck.
	 * 尝试将事件传输到用户空间。如果我们得到0个事件，并且还有超时时间，我们将再次尝试以获得更多运气
	 */
	res = ep_send_events(ep, events, maxevents);
	if (res > 0)
		ep_suspend_napi_irqs(ep);
	return res;
}

static int ep_schedule_timeout(ktime_t *to)
{
	if (to)
		return ktime_after(*to, ktime_get());
	else
		return 1;
}

/**
 * ep_poll - Retrieves ready events, and delivers them to the caller-supplied
 *           event buffer.
 *           检索已准备好的事件，并将它们传递给调用者提供的事件缓冲区
 *
 * @ep: Pointer to the eventpoll context. 指向 eventpoll 上下文的指针
 * @events: Pointer to the userspace buffer where the ready events should be
 *          stored.
 *          指向用户缓冲区的指针，就绪事件存储在此
 * @maxevents: Size (in terms of number of events) of the caller event buffer.调用者事件缓冲区大小（以事件数量表示）
 *
 * @timeout: Maximum timeout for the ready events fetch operation, in
 *           timespec. If the timeout is zero, the function will not block,
 *           while if the @timeout ptr is NULL, the function will block
 *           until at least one event has been retrieved (or an error
 *           occurred).
 *           准备事件获取操作的最大 超时事件。如果为0，函数不会阻塞，然而如果为null，函数将阻塞直到有一个事件发生或发生异常
 *
 * Return: the number of ready events which have been fetched, or an
 *          error code, in case of error.
 */
static int ep_poll(struct eventpoll *ep, struct epoll_event __user *events,
		   int maxevents, struct timespec64 *timeout)
{
	int res, eavail, timed_out = 0;
	u64 slack = 0;
	wait_queue_entry_t wait;
	ktime_t expires, *to = NULL;

	lockdep_assert_irqs_enabled();

	if (timeout && (timeout->tv_sec | timeout->tv_nsec)) {
		slack = select_estimate_accuracy(timeout);
		to = &expires;
		*to = timespec64_to_ktime(*timeout);
	} else if (timeout) {
		/*
		 * Avoid the unnecessary trip to the wait queue loop, if the
		 * caller specified a non blocking operation.
		 */
		timed_out = 1;
	}

	/*
	 * This call is racy: We may or may not see events that are being added
	 * to the ready list under the lock (e.g., in IRQ callbacks). For cases
	 * with a non-zero timeout, this thread will check the ready list under
	 * lock and will add to the wait queue.  For cases with a zero
	 * timeout, the user by definition should not care and will have to
	 * recheck again.
	 * 这个调用是动态的：我们可能会也可能不会看到正在被添加到锁下的就绪列表中的事件。
	 * 对于非零超时的情况，该线程将检查锁下的就绪列表并将其添加到等待队列中。
	 * 对于超时为零的情况，用户应该不用关心，并且必须再次检查
	 */
	eavail = ep_events_available(ep);

	while (1) {
		//若事件已就绪
		if (eavail) {
			//尝试发送事件
			res = ep_try_send_events(ep, events, maxevents);
			if (res)
				return res;
		}

		if (timed_out)
			return 0;

		eavail = ep_busy_loop(ep);
		if (eavail)
			continue;

		if (signal_pending(current))
			return -EINTR;

		/*
		 * Internally init_wait() uses autoremove_wake_function(),
		 * thus wait entry is removed from the wait queue on each
		 * wakeup. Why it is important? In case of several waiters
		 * each new wakeup will hit the next waiter, giving it the
		 * chance to harvest new event. Otherwise wakeup can be
		 * lost. This is also good performance-wise, because on
		 * normal wakeup path no need to call __remove_wait_queue()
		 * explicitly, thus ep->lock is not taken, which halts the
		 * event delivery.
		 * 在内部init_wait() 使用 autoremove_wake_function()，因此等待条目在每次唤醒时从等待队列中删除。
		 * 为什么它很重要？在几个等待者的情况下，每个新的唤醒将集中下一个等待者，给它机会收货新的事件，否则唤醒可能会丢失。
		 * 这在性能方面也很好，因为在正常的唤醒路径上不需要显示的调用 __remove_wait_queue，因此不会采取 ep->lock 锁，这会停止事件传递
		 *
		 * In fact, we now use an even more aggressive function that
		 * unconditionally removes, because we don't reuse the wait
		 * entry between loop iterations. This lets us also avoid the
		 * performance issue if a process is killed, causing all of its
		 * threads to wake up without being removed normally.
		 * 实际上，我们现在使用了一个更加激进的函数，它无条件的删除，因为我们不会在循环迭代直接重用等待条目。如果一个进程被杀死，导致他的所有线程在没有被正常移除的情况下被唤醒，这也让我们避免了性能问题
		 */
		init_wait(&wait);
		wait.func = ep_autoremove_wake_function;

		write_lock_irq(&ep->lock);
		/*
		 * Barrierless variant, waitqueue_active() is called under
		 * the same lock on wakeup ep_poll_callback() side, so it
		 * is safe to avoid an explicit barrier.
		 * 无屏障的变体，waitqueue_active 在唤醒 ep_poll_callback  端的相同锁下被调用，因此避免显示屏障是安全的
		 */
		__set_current_state(TASK_INTERRUPTIBLE);

		/*
		 * Do the final check under the lock. ep_start/done_scan()
		 * plays with two lists (->rdllist and ->ovflist) and there
		 * is always a race when both lists are empty for short
		 * period of time although events are pending, so lock is
		 * important.
		 * 在锁下做最后的检查，ep_start/done_scan() 使用两个列表 (->rdllist and ->ovflist)  ，当两个列表在短时间内为空时总是存在竞争，尽管事件正在挂起，因此锁很重要
		 */
		eavail = ep_events_available(ep);
		if (!eavail)
			//把新 waitqueue 添加到 epoll->wq 链表里
			__add_wait_queue_exclusive(&ep->wq, &wait);

		write_unlock_irq(&ep->lock);

		if (!eavail)
			timed_out = !ep_schedule_timeout(to) ||
				    //让出cpu 主动进入睡眠
				!schedule_hrtimeout_range(to, slack,
							  HRTIMER_MODE_ABS);
		__set_current_state(TASK_RUNNING);

		/*
		 * We were woken up, thus go and try to harvest some events.
		 * If timed out and still on the wait queue, recheck eavail
		 * carefully under lock, below.
		 */
		eavail = 1;

		if (!list_empty_careful(&wait.entry)) {
			write_lock_irq(&ep->lock);
			/*
			 * If the thread timed out and is not on the wait queue,
			 * it means that the thread was woken up after its
			 * timeout expired before it could reacquire the lock.
			 * Thus, when wait.entry is empty, it needs to harvest
			 * events.
			 */
			if (timed_out)
				eavail = list_empty(&wait.entry);
			__remove_wait_queue(&ep->wq, &wait);
			write_unlock_irq(&ep->lock);
		}
	}
}

/**
 * ep_loop_check_proc - verify that adding an epoll file inside another
 *                      epoll structure does not violate the constraints, in
 *                      terms of closed loops, or too deep chains (which can
 *                      result in excessive stack usage).
 *
 * @ep: the &struct eventpoll to be currently checked.
 * @depth: Current depth of the path being checked.
 *
 * Return: %zero if adding the epoll @file inside current epoll
 *          structure @ep does not violate the constraints, or %-1 otherwise.
 */
static int ep_loop_check_proc(struct eventpoll *ep, int depth)
{
	int error = 0;
	struct rb_node *rbp;
	struct epitem *epi;

	mutex_lock_nested(&ep->mtx, depth + 1);
	ep->gen = loop_check_gen;
	for (rbp = rb_first_cached(&ep->rbr); rbp; rbp = rb_next(rbp)) {
		epi = rb_entry(rbp, struct epitem, rbn);
		if (unlikely(is_file_epoll(epi->ffd.file))) {
			struct eventpoll *ep_tovisit;
			ep_tovisit = epi->ffd.file->private_data;
			if (ep_tovisit->gen == loop_check_gen)
				continue;
			if (ep_tovisit == inserting_into || depth > EP_MAX_NESTS)
				error = -1;
			else
				error = ep_loop_check_proc(ep_tovisit, depth + 1);
			if (error != 0)
				break;
		} else {
			/*
			 * If we've reached a file that is not associated with
			 * an ep, then we need to check if the newly added
			 * links are going to add too many wakeup paths. We do
			 * this by adding it to the tfile_check_list, if it's
			 * not already there, and calling reverse_path_check()
			 * during ep_insert().
			 */
			list_file(epi->ffd.file);
		}
	}
	mutex_unlock(&ep->mtx);

	return error;
}

/**
 * ep_loop_check - Performs a check to verify that adding an epoll file (@to)
 *                 into another epoll file (represented by @ep) does not create
 *                 closed loops or too deep chains.
 *
 * @ep: Pointer to the epoll we are inserting into.
 * @to: Pointer to the epoll to be inserted.
 *
 * Return: %zero if adding the epoll @to inside the epoll @from
 * does not violate the constraints, or %-1 otherwise.
 */
static int ep_loop_check(struct eventpoll *ep, struct eventpoll *to)
{
	inserting_into = ep;
	return ep_loop_check_proc(to, 0);
}

static void clear_tfile_check_list(void)
{
	rcu_read_lock();
	while (tfile_check_list != EP_UNACTIVE_PTR) {
		struct epitems_head *head = tfile_check_list;
		tfile_check_list = head->next;
		unlist_file(head);
	}
	rcu_read_unlock();
}

/*
 * Open an eventpoll file descriptor.
 * 打开一个 eventpoll 文件描述符
 */
static int do_epoll_create(int flags)
{
	int error, fd;
	struct eventpoll *ep = NULL;
	struct file *file;

	/* Check the EPOLL_* constant for consistency. 检查 epoll常数是否一致 */
	BUILD_BUG_ON(EPOLL_CLOEXEC != O_CLOEXEC);

	if (flags & ~EPOLL_CLOEXEC)
		return -EINVAL;
	/*
	 * Create the internal data structure ("struct eventpoll").
	 * 创建内部数据结构 eventpoll
	 */
	error = ep_alloc(&ep);
	if (error < 0)
		return error;
	/*
	 * Creates all the items needed to setup an eventpoll file. That is,
	 * a file structure and a free file descriptor.
	 * 创建设置 eventpoll 文件所需的所有项，也就是说，一个文件和一个空闲文件描述符
	 */
	fd = get_unused_fd_flags(O_RDWR | (flags & O_CLOEXEC));
	if (fd < 0) {
		error = fd;
		goto out_free_ep;
	}
	file = anon_inode_getfile("[eventpoll]", &eventpoll_fops, ep,
				 O_RDWR | (flags & O_CLOEXEC));
	if (IS_ERR(file)) {
		error = PTR_ERR(file);
		goto out_free_fd;
	}
	//设置 epoll文件
	ep->file = file;
	//将文件安装到文件数组中
	fd_install(fd, file);
	return fd;

out_free_fd:
	put_unused_fd(fd);
out_free_ep:
	ep_clear_and_put(ep);
	return error;
}

SYSCALL_DEFINE1(epoll_create1, int, flags)
{
	return do_epoll_create(flags);
}

SYSCALL_DEFINE1(epoll_create, int, size)
{
	if (size <= 0)
		return -EINVAL;

	return do_epoll_create(0);
}

#ifdef CONFIG_PM_SLEEP
static inline void ep_take_care_of_epollwakeup(struct epoll_event *epev)
{
	if ((epev->events & EPOLLWAKEUP) && !capable(CAP_BLOCK_SUSPEND))
		epev->events &= ~EPOLLWAKEUP;
}
#else
static inline void ep_take_care_of_epollwakeup(struct epoll_event *epev)
{
	epev->events &= ~EPOLLWAKEUP;
}
#endif

static inline int epoll_mutex_lock(struct mutex *mutex, int depth,
				   bool nonblock)
{
	if (!nonblock) {
		mutex_lock_nested(mutex, depth);
		return 0;
	}
	if (mutex_trylock(mutex))
		return 0;
	return -EAGAIN;
}

// 添加socket到 epoll 对象中
int do_epoll_ctl(int epfd, int op, int fd, struct epoll_event *epds,
		 bool nonblock)
{
	int error;
	int full_check = 0;
	//声明 eventpoll 对象
	struct eventpoll *ep;
	//声明 epitem 对象
	struct epitem *epi;
	struct eventpoll *tep = NULL;

	CLASS(fd, f)(epfd);
	if (fd_empty(f))
		return -EBADF;

	/* Get the "struct file *" for the target file
	 * 获取目标文件的 struct file */
	CLASS(fd, tf)(fd);
	if (fd_empty(tf))
		return -EBADF;

	/* The target file descriptor must support poll
	 * 目标文件描述符必须支持 poll
	 * */
	if (!file_can_poll(fd_file(tf)))
		return -EPERM;

	/* Check if EPOLLWAKEUP is allowed
	 * 检查是否允许 EPOLLWAKEUP
	 * */
	if (ep_op_has_event(op))
		ep_take_care_of_epollwakeup(epds);

	/*
	 * We have to check that the file structure underneath the file descriptor
	 * the user passed to us _is_ an eventpoll file. And also we do not permit
	 * adding an epoll file descriptor inside itself.
	 * 检查用户传给我们的文件描述符下面的文件结构是 eventpoll 文件。我们也不允许在文件里面添加 epoll 文件
	 */
	error = -EINVAL;
	if (fd_file(f) == fd_file(tf) || !is_file_epoll(fd_file(f)))
		goto error_tgt_fput;

	/*
	 * epoll adds to the wakeup queue at EPOLL_CTL_ADD time only,
	 * so EPOLLEXCLUSIVE is not allowed for a EPOLL_CTL_MOD operation.
	 * Also, we do not currently supported nested exclusive wakeups.
	 * epoll 添加唤醒队列 只在EPOLL_CTL_ADD时刻，所以 EPOLL_CTL_MOD操作不允许使用 EPOLLEXCLUSIVE。
	 * 另外，我们目前不支持嵌套的独占唤醒
	 */
	if (ep_op_has_event(op) && (epds->events & EPOLLEXCLUSIVE)) {
		if (op == EPOLL_CTL_MOD)
			goto error_tgt_fput;
		if (op == EPOLL_CTL_ADD && (is_file_epoll(fd_file(tf)) ||
				(epds->events & ~EPOLLEXCLUSIVE_OK_BITS)))
			goto error_tgt_fput;
	}

	/*
	 * At this point it is safe to assume that the "private_data" contains
	 * our own data structure.
	 * 此时可以安全的假设 private_data 包含我们自己的数据结构
	 */
	ep = fd_file(f)->private_data;

	/*
	 * When we insert an epoll file descriptor inside another epoll file
	 * descriptor, there is the chance of creating closed loops, which are
	 * better be handled here, than in more critical paths. While we are
	 * checking for loops we also determine the list of files reachable
	 * and hang them on the tfile_check_list, so we can check that we
	 * haven't created too many possible wakeup paths.
	 * 当我们插入一个 epoll文件描述符到另一个 epoll文件描述符时，有可能产生闭环，最好在这里处理，而不是在更关键的路径上处理。
	 * 当我们检查循环时，我们也确定了可到达的文件列表，并将他们挂载到了 tfile_check_list，这样我们就可以检查我们没有创建太多可能唤醒路径
	 *
	 * We do not need to take the global 'epumutex' on EPOLL_CTL_ADD when
	 * the epoll file descriptor is attaching directly to a wakeup source,
	 * unless the epoll file descriptor is nested. The purpose of taking the
	 * 'epnested_mutex' on add is to prevent complex toplogies such as loops and
	 * deep wakeup paths from forming in parallel through multiple
	 * EPOLL_CTL_ADD operations.
	 * 当 epoll 文件描述符直接附加到唤醒源时，我们不需要再 EPOLL_CTL_ADD 上使用全局 epumutex ，除非 epoll文件描述符时嵌套的。
	 * 在 add 上使用 epnested_mutex 的目的是防止复杂的拓扑结构，如循环和深度唤醒路径，通过多个 EPOLL_CTL_ADD 操作并形成
	 */
	error = epoll_mutex_lock(&ep->mtx, 0, nonblock);
	if (error)
		goto error_tgt_fput;
	//如果是插入操作
	if (op == EPOLL_CTL_ADD) {
		if (READ_ONCE(fd_file(f)->f_ep) || ep->gen == loop_check_gen ||
		    is_file_epoll(fd_file(tf))) {
			mutex_unlock(&ep->mtx);
			error = epoll_mutex_lock(&epnested_mutex, 0, nonblock);
			if (error)
				goto error_tgt_fput;
			loop_check_gen++;
			full_check = 1;
			if (is_file_epoll(fd_file(tf))) {
				tep = fd_file(tf)->private_data;
				error = -ELOOP;
				if (ep_loop_check(ep, tep) != 0)
					goto error_tgt_fput;
			}
			error = epoll_mutex_lock(&ep->mtx, 0, nonblock);
			if (error)
				goto error_tgt_fput;
		}
	}

	/*
	 * Try to lookup the file inside our RB tree. Since we grabbed "mtx"
	 * above, we can be sure to be able to use the item looked up by
	 * ep_find() till we release the mutex.
	 * 尝试从 RB树中寻找文件。
	 * 由于我们在上面抓取了 mtx，我们可以确保能够使用 ep_find 查找的项，直到释放锁
	 */
	//根据当前文件找到 epitem
	epi = ep_find(ep, fd_file(tf), fd);

	error = -EINVAL;
	switch (op) {
		//新增操作
	case EPOLL_CTL_ADD:
		if (!epi) {
			epds->events |= EPOLLERR | EPOLLHUP;
			//插入到 eventpoll
			error = ep_insert(ep, epds, fd_file(tf), fd, full_check);
		} else
			error = -EEXIST;
		break;
		//删除操作
	case EPOLL_CTL_DEL:
		if (epi) {
			/*
			 * The eventpoll itself is still alive: the refcount
			 * can't go to zero here.
			 */
			ep_remove_safe(ep, epi);
			error = 0;
		} else {
			error = -ENOENT;
		}
		break;
		//修改操作
	case EPOLL_CTL_MOD:
		if (epi) {
			if (!(epi->event.events & EPOLLEXCLUSIVE)) {
				epds->events |= EPOLLERR | EPOLLHUP;
				error = ep_modify(ep, epi, epds);
			}
		} else
			error = -ENOENT;
		break;
	}
	mutex_unlock(&ep->mtx);

error_tgt_fput:
	if (full_check) {
		clear_tfile_check_list();
		loop_check_gen++;
		mutex_unlock(&epnested_mutex);
	}
	return error;
}

/*
 * The following function implements the controller interface for
 * the eventpoll file that enables the insertion/removal/change of
 * file descriptors inside the interest set.
 * 下面的函数实现了 eventpoll 文件的控制器接口，该接口支持在兴趣集中插入删除更改描述符
 */
SYSCALL_DEFINE4(epoll_ctl, int, epfd, int, op, int, fd,
		struct epoll_event __user *, event)
{
	struct epoll_event epds;

	if (ep_op_has_event(op) &&
	    copy_from_user(&epds, event, sizeof(struct epoll_event)))
		return -EFAULT;

	return do_epoll_ctl(epfd, op, fd, &epds, false);
}

static int ep_check_params(struct file *file, struct epoll_event __user *evs,
			   int maxevents)
{
	/* The maximum number of event must be greater than zero */
	if (maxevents <= 0 || maxevents > EP_MAX_EVENTS)
		return -EINVAL;

	/* Verify that the area passed by the user is writeable */
	if (!access_ok(evs, maxevents * sizeof(struct epoll_event)))
		return -EFAULT;

	/*
	 * We have to check that the file structure underneath the fd
	 * the user passed to us _is_ an eventpoll file.
	 */
	if (!is_file_epoll(file))
		return -EINVAL;

	return 0;
}

int epoll_sendevents(struct file *file, struct epoll_event __user *events,
		     int maxevents)
{
	struct eventpoll *ep;
	int ret;

	ret = ep_check_params(file, events, maxevents);
	if (unlikely(ret))
		return ret;

	ep = file->private_data;
	/*
	 * Racy call, but that's ok - it should get retried based on
	 * poll readiness anyway.
	 */
	if (ep_events_available(ep))
		return ep_try_send_events(ep, events, maxevents);
	return 0;
}

/*
 * Implement the event wait interface for the eventpoll file. It is the kernel
 * part of the user space epoll_wait(2).
 * 为 eventpoll 文件实现事件等待接口。他是用户空间 epoll_wait 的内核部分
 */
static int do_epoll_wait(int epfd, struct epoll_event __user *events,
			 int maxevents, struct timespec64 *to)
{
	struct eventpoll *ep;
	int ret;

	/* Get the "struct file *" for the eventpoll file */
	CLASS(fd, f)(epfd);
	if (fd_empty(f))
		return -EBADF;

	ret = ep_check_params(fd_file(f), events, maxevents);
	if (unlikely(ret))
		return ret;

	/*
	 * At this point it is safe to assume that the "private_data" contains
	 * our own data structure.
	 * 此时可以安全的假设 private_data 包含我们自己的数据结构
	 */
	ep = fd_file(f)->private_data;

	/* Time to fish for events 是时候去寻找数据了 ... */
	return ep_poll(ep, events, maxevents, to);
}

SYSCALL_DEFINE4(epoll_wait, int, epfd, struct epoll_event __user *, events,
		int, maxevents, int, timeout)
{
	struct timespec64 to;

	return do_epoll_wait(epfd, events, maxevents,
			     ep_timeout_to_timespec(&to, timeout));
}

/*
 * Implement the event wait interface for the eventpoll file. It is the kernel
 * part of the user space epoll_pwait(2).
 */
static int do_epoll_pwait(int epfd, struct epoll_event __user *events,
			  int maxevents, struct timespec64 *to,
			  const sigset_t __user *sigmask, size_t sigsetsize)
{
	int error;

	/*
	 * If the caller wants a certain signal mask to be set during the wait,
	 * we apply it here.
	 */
	error = set_user_sigmask(sigmask, sigsetsize);
	if (error)
		return error;

	error = do_epoll_wait(epfd, events, maxevents, to);

	restore_saved_sigmask_unless(error == -EINTR);

	return error;
}

SYSCALL_DEFINE6(epoll_pwait, int, epfd, struct epoll_event __user *, events,
		int, maxevents, int, timeout, const sigset_t __user *, sigmask,
		size_t, sigsetsize)
{
	struct timespec64 to;

	return do_epoll_pwait(epfd, events, maxevents,
			      ep_timeout_to_timespec(&to, timeout),
			      sigmask, sigsetsize);
}

SYSCALL_DEFINE6(epoll_pwait2, int, epfd, struct epoll_event __user *, events,
		int, maxevents, const struct __kernel_timespec __user *, timeout,
		const sigset_t __user *, sigmask, size_t, sigsetsize)
{
	struct timespec64 ts, *to = NULL;

	if (timeout) {
		if (get_timespec64(&ts, timeout))
			return -EFAULT;
		to = &ts;
		if (poll_select_set_timeout(to, ts.tv_sec, ts.tv_nsec))
			return -EINVAL;
	}

	return do_epoll_pwait(epfd, events, maxevents, to,
			      sigmask, sigsetsize);
}

#ifdef CONFIG_COMPAT
static int do_compat_epoll_pwait(int epfd, struct epoll_event __user *events,
				 int maxevents, struct timespec64 *timeout,
				 const compat_sigset_t __user *sigmask,
				 compat_size_t sigsetsize)
{
	long err;

	/*
	 * If the caller wants a certain signal mask to be set during the wait,
	 * we apply it here.
	 */
	err = set_compat_user_sigmask(sigmask, sigsetsize);
	if (err)
		return err;

	err = do_epoll_wait(epfd, events, maxevents, timeout);

	restore_saved_sigmask_unless(err == -EINTR);

	return err;
}

COMPAT_SYSCALL_DEFINE6(epoll_pwait, int, epfd,
		       struct epoll_event __user *, events,
		       int, maxevents, int, timeout,
		       const compat_sigset_t __user *, sigmask,
		       compat_size_t, sigsetsize)
{
	struct timespec64 to;

	return do_compat_epoll_pwait(epfd, events, maxevents,
				     ep_timeout_to_timespec(&to, timeout),
				     sigmask, sigsetsize);
}

COMPAT_SYSCALL_DEFINE6(epoll_pwait2, int, epfd,
		       struct epoll_event __user *, events,
		       int, maxevents,
		       const struct __kernel_timespec __user *, timeout,
		       const compat_sigset_t __user *, sigmask,
		       compat_size_t, sigsetsize)
{
	struct timespec64 ts, *to = NULL;

	if (timeout) {
		if (get_timespec64(&ts, timeout))
			return -EFAULT;
		to = &ts;
		if (poll_select_set_timeout(to, ts.tv_sec, ts.tv_nsec))
			return -EINVAL;
	}

	return do_compat_epoll_pwait(epfd, events, maxevents, to,
				     sigmask, sigsetsize);
}

#endif

static int __init eventpoll_init(void)
{
	struct sysinfo si;

	si_meminfo(&si);
	/*
	 * Allows top 4% of lomem to be allocated for epoll watches (per user).
	 */
	max_user_watches = (((si.totalram - si.totalhigh) / 25) << PAGE_SHIFT) /
		EP_ITEM_COST;
	BUG_ON(max_user_watches < 0);

	/*
	 * We can have many thousands of epitems, so prevent this from
	 * using an extra cache line on 64-bit (and smaller) CPUs
	 */
	BUILD_BUG_ON(sizeof(void *) <= 8 && sizeof(struct epitem) > 128);

	/* Allocates slab cache used to allocate "struct epitem" items */
	epi_cache = kmem_cache_create("eventpoll_epi", sizeof(struct epitem),
			0, SLAB_HWCACHE_ALIGN|SLAB_PANIC|SLAB_ACCOUNT, NULL);

	/* Allocates slab cache used to allocate "struct eppoll_entry" */
	pwq_cache = kmem_cache_create("eventpoll_pwq",
		sizeof(struct eppoll_entry), 0, SLAB_PANIC|SLAB_ACCOUNT, NULL);
	epoll_sysctls_init();

	ephead_cache = kmem_cache_create("ep_head",
		sizeof(struct epitems_head), 0, SLAB_PANIC|SLAB_ACCOUNT, NULL);

	return 0;
}
fs_initcall(eventpoll_init);
