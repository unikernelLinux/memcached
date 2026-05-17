/* -*- Mode: C; tab-width: 4; c-basic-offset: 4; indent-tabs-mode: nil -*- */
/*
 * Thread management for memcached.
 */
#include "memcached.h"
#ifdef EXTSTORE
#include "storage.h"
#endif
#ifdef PROXY
#include "proto_proxy.h"
#endif
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>

#include "queue.h"
#include "tls.h"

#ifdef __sun
#include <atomic.h>
#endif

#define UPCALL_BUF_COUNT 128

/* Locks for cache LRU operations */
pthread_mutex_t lru_locks[POWER_LARGEST];

/* Connection lock around accepting new connections */
pthread_mutex_t conn_lock = PTHREAD_MUTEX_INITIALIZER;

#if !defined(HAVE_GCC_ATOMICS) && !defined(__sun)
pthread_mutex_t atomics_mutex = PTHREAD_MUTEX_INITIALIZER;
#endif

/* Lock for global stats */
static pthread_mutex_t stats_lock = PTHREAD_MUTEX_INITIALIZER;

/* Lock to cause worker threads to hang up after being woken */
static pthread_mutex_t worker_hang_lock;

static pthread_mutex_t *item_locks;
/* size of the item lock hash table */
static uint32_t item_lock_count;
static unsigned int item_lock_hashpower;
#define hashsize(n) ((unsigned long int)1<<(n))
#define hashmask(n) (hashsize(n)-1)

/* Worker threads */
static LIBEVENT_THREAD *threads;

/* Thread-local pointer to the current worker thread struct */
__thread LIBEVENT_THREAD *worker_me;

/*
 * Number of worker threads that have finished setting themselves up.
 */
static int init_count = 0;
static pthread_mutex_t init_lock;
static pthread_cond_t init_cond;

/* Second-phase "go" signal: released after server_sockets populates listen_conn */
static pthread_mutex_t go_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t go_cond = PTHREAD_COND_INITIALIZER;
static bool workers_should_go = false;

/* item_lock() must be held for an item before any modifications to either its
 * associated hash bucket, or the structure itself.
 * LRU modifications must hold the item lock, and the LRU lock.
 * LRU's accessing items must item_trylock() before modifying an item.
 * Items accessible from an LRU must not be freed or modified
 * without first locking and removing from the LRU.
 */

void item_lock(uint32_t hv) {
    mutex_lock(&item_locks[hv & hashmask(item_lock_hashpower)]);
}

void *item_trylock(uint32_t hv) {
    pthread_mutex_t *lock = &item_locks[hv & hashmask(item_lock_hashpower)];
    if (pthread_mutex_trylock(lock) == 0) {
        return lock;
    }
    return NULL;
}

void item_trylock_unlock(void *lock) {
    mutex_unlock((pthread_mutex_t *) lock);
}

void item_unlock(uint32_t hv) {
    mutex_unlock(&item_locks[hv & hashmask(item_lock_hashpower)]);
}

static void wait_for_thread_registration(int nthreads) {
    while (init_count < nthreads) {
        pthread_cond_wait(&init_cond, &init_lock);
    }
}

static void register_thread_initialized(void) {
    pthread_mutex_lock(&init_lock);
    init_count++;
    pthread_cond_signal(&init_cond);
    pthread_mutex_unlock(&init_lock);
    /* Force worker threads to pile up if someone wants us to */
    pthread_mutex_lock(&worker_hang_lock);
    pthread_mutex_unlock(&worker_hang_lock);
}

/* Must not be called with any deeper locks held */
void pause_threads(enum pause_thread_types type) {
    switch (type) {
        case PAUSE_ALL_THREADS:
            slab_maintenance_pause(settings.slab_rebal);
            lru_maintainer_pause();
            lru_crawler_pause();
#ifdef EXTSTORE
            storage_compact_pause();
            storage_write_pause();
#endif
        case PAUSE_WORKER_THREADS:
            pthread_mutex_lock(&worker_hang_lock);
            break;
        case RESUME_ALL_THREADS:
            slab_maintenance_resume(settings.slab_rebal);
            lru_maintainer_resume();
            lru_crawler_resume();
#ifdef EXTSTORE
            storage_compact_resume();
            storage_write_resume();
#endif
        case RESUME_WORKER_THREADS:
            pthread_mutex_unlock(&worker_hang_lock);
            break;
        default:
            fprintf(stderr, "Unknown lock type: %d\n", type);
            assert(1 == 0);
            break;
    }
}

// MUST not be called with any deeper locks held
// MUST be called only by parent thread
void stop_threads(void) {
    int i;

    stop_assoc_maintenance_thread();
    if (settings.verbose > 0)
        fprintf(stderr, "stopped assoc\n");

    stop_item_crawler_thread(CRAWLER_WAIT);
    if (settings.verbose > 0)
        fprintf(stderr, "stopped lru crawler\n");
    if (settings.lru_maintainer_thread) {
        stop_lru_maintainer_thread();
        if (settings.verbose > 0)
            fprintf(stderr, "stopped maintainer\n");
    }
    if (settings.slab_reassign) {
        stop_slab_maintenance_thread(settings.slab_rebal);
        if (settings.verbose > 0)
            fprintf(stderr, "stopped slab mover\n");
    }
    logger_stop();
    if (settings.verbose > 0)
        fprintf(stderr, "stopped logger thread\n");
    stop_conn_timeout_thread();
    if (settings.verbose > 0)
        fprintf(stderr, "stopped idle timeout thread\n");

    conn_close_all();

    /* Close the upcall fd to unblock workers */
    if (upfd >= 0) {
        close(upfd);
        upfd = -1;
    }

    for (i = 0; i < settings.num_threads; i++) {
        pthread_join(threads[i].thread_id, NULL);
    }

    if (settings.verbose > 0)
        fprintf(stderr, "all background threads stopped\n");
}

/*
 * Creates a worker thread.
 */
static void create_worker(void *(*func)(void *), void *arg) {
    pthread_attr_t  attr;
    int             ret;

    pthread_attr_init(&attr);

    if ((ret = pthread_create(&((LIBEVENT_THREAD*)arg)->thread_id, &attr, func, arg)) != 0) {
        fprintf(stderr, "Can't create thread: %s\n",
                strerror(ret));
        exit(1);
    }

    thread_setname(((LIBEVENT_THREAD*)arg)->thread_id, "mc-worker");
}

/*
 * Close a connection from a side thread. With upcalls/PCACHE, we can drive
 * the state machine directly since any worker can handle any connection.
 */
void sidethread_conn_close(conn *c) {
    conn_set_state(c, conn_closing);
    conn_worker_readd(c);
}

/*
 * Sets whether or not we accept new connections.
 */
void accept_new_conns(const bool do_accept) {
    pthread_mutex_lock(&conn_lock);
    do_accept_new_conns(do_accept);
    pthread_mutex_unlock(&conn_lock);
}

/*
 * Set up a thread's information.
 */
static void setup_thread(LIBEVENT_THREAD *me) {
    pthread_mutex_init(&me->stats.mutex, NULL);

    me->rbuf_cache = cache_create("rbuf", READ_BUFFER_SIZE, sizeof(char *));
    if (me->rbuf_cache == NULL) {
        fprintf(stderr, "Failed to create read buffer cache\n");
        exit(EXIT_FAILURE);
    }
    if (settings.read_buf_mem_limit) {
        int limit = settings.read_buf_mem_limit / settings.num_threads;
        if (limit < READ_BUFFER_SIZE) {
            limit = 1;
        } else {
            limit = limit / READ_BUFFER_SIZE;
        }
        cache_set_limit(me->rbuf_cache, limit);
    }

    me->io_cache = cache_create("io", sizeof(io_pending_t), sizeof(char*));
    if (me->io_cache == NULL) {
        fprintf(stderr, "Failed to create IO object cache\n");
        exit(EXIT_FAILURE);
    }
#ifdef TLS
    if (settings.ssl_enabled) {
        me->ssl_wbuf = (char *)malloc((size_t)settings.ssl_wbuf_size);
        if (me->ssl_wbuf == NULL) {
            fprintf(stderr, "Failed to allocate the SSL write buffer\n");
            exit(EXIT_FAILURE);
        }
    }
#endif
#ifdef EXTSTORE
    if (me->storage) {
        thread_io_queue_add(me, IO_QUEUE_EXTSTORE, me->storage,
            storage_submit_cb);
    }
#endif
#ifdef PROXY
    thread_io_queue_add(me, IO_QUEUE_PROXY, settings.proxy_ctx, proxy_submit_cb);

    if (settings.proxy_enabled) {
        proxy_thread_init(settings.proxy_ctx, me);
    }
#endif
    thread_io_queue_add(me, IO_QUEUE_NONE, NULL, NULL);
}

/*
 * Worker thread: upcall event loop
 */
static void *worker_upcall(void *arg) {
    LIBEVENT_THREAD *me_thread = arg;
    worker_me = me_thread;

    me_thread->l = logger_create();
    me_thread->lru_bump_buf = item_lru_bump_buf_create();
    if (me_thread->l == NULL || me_thread->lru_bump_buf == NULL) {
        abort();
    }

    if (settings.drop_privileges) {
        drop_worker_privileges();
    }

    upcall_worker_setup(upfd, UPCALL_BUF_COUNT, READ_BUFFER_SIZE);

    register_thread_initialized();

    /* Wait for main thread to finish server_sockets and signal go. */
    pthread_mutex_lock(&go_lock);
    while (!workers_should_go)
        pthread_cond_wait(&go_cond, &go_lock);
    pthread_mutex_unlock(&go_lock);

    /* Thread 0 registers accepts for all listen sockets.
     * With the single-anchor-per-fd invariant, only one anchor can be active
     * per fd at a time; the callback re-registers after each accept. */
    if (me_thread->thread_baseid == 0) {
        for (conn *c = listen_conn; c; c = c->next) {
            add_accept(c->sfd, upcall_accept_cb);
        }
    }

    run_event_loop(upfd, 1);

    register_thread_initialized();
    return NULL;
}

// Interface is slightly different on various platforms.
// On linux, at least, the len limit is 16 bytes.
#define THR_NAME_MAXLEN 16
void thread_setname(pthread_t thread, const char *name) {
assert(strlen(name) < THR_NAME_MAXLEN);
#if defined(__linux__) && defined(HAVE_PTHREAD_SETNAME_NP)
pthread_setname_np(thread, name);
#endif
}
#undef THR_NAME_MAXLEN

// NOTE: need better encapsulation.
// used by the proxy module to iterate the worker threads.
LIBEVENT_THREAD *get_worker_thread(int id) {
    return &threads[id];
}

/********************************* ITEM ACCESS *******************************/

/*
 * Allocates a new item.
 */
item *item_alloc(const char *key, size_t nkey, client_flags_t flags, rel_time_t exptime, int nbytes) {
    item *it;
    /* do_item_alloc handles its own locks */
    it = do_item_alloc(key, nkey, flags, exptime, nbytes);
    return it;
}

/*
 * Returns an item if it hasn't been marked as expired,
 * lazy-expiring as needed.
 */
item *item_get(const char *key, const size_t nkey, LIBEVENT_THREAD *t, const bool do_update) {
    item *it;
    uint32_t hv;
    hv = hash(key, nkey);
    item_lock(hv);
    it = do_item_get(key, nkey, hv, t, do_update);
    item_unlock(hv);
    return it;
}

// returns an item with the item lock held.
// lock will still be held even if return is NULL, allowing caller to replace
// an item atomically if desired.
item *item_get_locked(const char *key, const size_t nkey, LIBEVENT_THREAD *t, const bool do_update, uint32_t *hv) {
    item *it;
    *hv = hash(key, nkey);
    item_lock(*hv);
    it = do_item_get(key, nkey, *hv, t, do_update);
    return it;
}

item *item_touch(const char *key, size_t nkey, uint32_t exptime, LIBEVENT_THREAD *t) {
    item *it;
    uint32_t hv;
    hv = hash(key, nkey);
    item_lock(hv);
    it = do_item_touch(key, nkey, exptime, hv, t);
    item_unlock(hv);
    return it;
}

/*
 * Decrements the reference count on an item and adds it to the freelist if
 * needed.
 */
void item_remove(item *item) {
    uint32_t hv;
    hv = hash(ITEM_key(item), item->nkey);

    item_lock(hv);
    do_item_remove(item);
    item_unlock(hv);
}

/*
 * Replaces one item with another in the hashtable.
 * Unprotected by a mutex lock since the core server does not require
 * it to be thread-safe.
 */
int item_replace(item *old_it, item *new_it, const uint32_t hv, const uint64_t cas_in) {
    return do_item_replace(old_it, new_it, hv, cas_in);
}

/*
 * Unlinks an item from the LRU and hashtable.
 */
void item_unlink(item *item) {
    uint32_t hv;
    hv = hash(ITEM_key(item), item->nkey);
    item_lock(hv);
    do_item_unlink(item, hv);
    item_unlock(hv);
}

/*
 * Does arithmetic on a numeric item value.
 */
enum delta_result_type add_delta(LIBEVENT_THREAD *t, const char *key,
                                 const size_t nkey, bool incr,
                                 const int64_t delta, char *buf,
                                 uint64_t *cas) {
    enum delta_result_type ret;
    uint32_t hv;

    hv = hash(key, nkey);
    item_lock(hv);
    ret = do_add_delta(t, key, nkey, incr, delta, buf, cas, hv, NULL);
    item_unlock(hv);
    return ret;
}

/*
 * Stores an item in the cache (high level, obeys set/add/replace semantics)
 */
enum store_item_type store_item(item *item, int comm, LIBEVENT_THREAD *t, int *nbytes, uint64_t *cas, const uint64_t cas_in, bool cas_stale) {
    enum store_item_type ret;
    uint32_t hv;

    hv = hash(ITEM_key(item), item->nkey);
    item_lock(hv);
    ret = do_store_item(item, comm, t, hv, nbytes, cas, cas_in, cas_stale);
    item_unlock(hv);
    return ret;
}

/******************************* GLOBAL STATS ******************************/

void STATS_LOCK(void) {
    pthread_mutex_lock(&stats_lock);
}

void STATS_UNLOCK(void) {
    pthread_mutex_unlock(&stats_lock);
}

void threadlocal_stats_reset(void) {
    int ii;
    for (ii = 0; ii < settings.num_threads; ++ii) {
        pthread_mutex_lock(&threads[ii].stats.mutex);
#define X(name) threads[ii].stats.name = 0;
        THREAD_STATS_FIELDS
#ifdef EXTSTORE
        EXTSTORE_THREAD_STATS_FIELDS
#endif
#ifdef PROXY
        PROXY_THREAD_STATS_FIELDS
#endif
#undef X

        memset(&threads[ii].stats.slab_stats, 0,
                sizeof(threads[ii].stats.slab_stats));
        memset(&threads[ii].stats.lru_hits, 0,
                sizeof(uint64_t) * POWER_LARGEST);

        pthread_mutex_unlock(&threads[ii].stats.mutex);
    }
}

void threadlocal_stats_aggregate(struct thread_stats *stats) {
    int ii, sid;

    /* The struct has a mutex, but we can safely set the whole thing
     * to zero since it is unused when aggregating. */
    memset(stats, 0, sizeof(*stats));

    for (ii = 0; ii < settings.num_threads; ++ii) {
        pthread_mutex_lock(&threads[ii].stats.mutex);
#define X(name) stats->name += threads[ii].stats.name;
        THREAD_STATS_FIELDS
#ifdef EXTSTORE
        EXTSTORE_THREAD_STATS_FIELDS
#endif
#ifdef PROXY
        PROXY_THREAD_STATS_FIELDS
        stats->proxy_req_active += threads[ii].stats.proxy_req_active;
#endif
#undef X

        for (sid = 0; sid < MAX_NUMBER_OF_SLAB_CLASSES; sid++) {
#define X(name) stats->slab_stats[sid].name += \
            threads[ii].stats.slab_stats[sid].name;
            SLAB_STATS_FIELDS
#undef X
        }

        for (sid = 0; sid < POWER_LARGEST; sid++) {
            stats->lru_hits[sid] +=
                threads[ii].stats.lru_hits[sid];
            stats->slab_stats[CLEAR_LRU(sid)].get_hits +=
                threads[ii].stats.lru_hits[sid];
        }

        stats->read_buf_count += threads[ii].rbuf_cache->total;
        stats->read_buf_bytes += threads[ii].rbuf_cache->total * READ_BUFFER_SIZE;
        stats->read_buf_bytes_free += threads[ii].rbuf_cache->freecurr * READ_BUFFER_SIZE;
        pthread_mutex_unlock(&threads[ii].stats.mutex);
    }
}

void slab_stats_aggregate(struct thread_stats *stats, struct slab_stats *out) {
    int sid;

    memset(out, 0, sizeof(*out));

    for (sid = 0; sid < MAX_NUMBER_OF_SLAB_CLASSES; sid++) {
#define X(name) out->name += stats->slab_stats[sid].name;
        SLAB_STATS_FIELDS
#undef X
    }
}

/*
 * Initializes the thread subsystem, creating various worker threads.
 *
 * nthreads  Number of worker event handler threads to spawn
 */
void memcached_thread_init(int nthreads, void *arg) {
    int         i;
    int         power;

    for (i = 0; i < POWER_LARGEST; i++) {
        pthread_mutex_init(&lru_locks[i], NULL);
    }
    pthread_mutex_init(&worker_hang_lock, NULL);

    pthread_mutex_init(&init_lock, NULL);
    pthread_cond_init(&init_cond, NULL);

    /* Want a wide lock table, but don't waste memory */
    if (nthreads < 3) {
        power = 10;
    } else if (nthreads < 4) {
        power = 11;
    } else if (nthreads < 5) {
        power = 12;
    } else if (nthreads <= 10) {
        power = 13;
    } else if (nthreads <= 20) {
        power = 14;
    } else {
        /* 32k buckets. just under the hashpower default. */
        power = 15;
    }

    if (power >= hashpower) {
        fprintf(stderr, "Hash table power size (%d) cannot be equal to or less than item lock table (%d)\n", hashpower, power);
        fprintf(stderr, "Item lock table grows with `-t N` (worker threadcount)\n");
        fprintf(stderr, "Hash table grows with `-o hashpower=N` \n");
        exit(1);
    }

    item_lock_count = hashsize(power);
    item_lock_hashpower = power;

    item_locks = calloc(item_lock_count, sizeof(pthread_mutex_t));
    if (! item_locks) {
        perror("Can't allocate item locks");
        exit(1);
    }
    for (i = 0; i < item_lock_count; i++) {
        pthread_mutex_init(&item_locks[i], NULL);
    }

    threads = calloc(nthreads, sizeof(LIBEVENT_THREAD));
    if (! threads) {
        perror("Can't allocate thread descriptors");
        exit(1);
    }

    for (i = 0; i < nthreads; i++) {
#ifdef EXTSTORE
        threads[i].storage = arg;
#endif
        threads[i].thread_baseid = i;
        setup_thread(&threads[i]);
    }

    /* Create threads after setup. */
    for (i = 0; i < nthreads; i++) {
        create_worker(worker_upcall, &threads[i]);
    }

    /* Wait for all the threads to set themselves up before returning. */
    pthread_mutex_lock(&init_lock);
    wait_for_thread_registration(nthreads);
    pthread_mutex_unlock(&init_lock);
}

void upcall_workers_go(void) {
    pthread_mutex_lock(&go_lock);
    workers_should_go = true;
    pthread_cond_broadcast(&go_cond);
    pthread_mutex_unlock(&go_lock);
}
