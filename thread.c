/* -*- Mode: C; tab-width: 4; c-basic-offset: 4; indent-tabs-mode: nil -*- */
/*
 * Thread management for memcached.
 */
#include "memcached.h"
#ifdef EXTSTORE
#include "storage.h"
#endif
#ifdef HAVE_EVENTFD
#include <sys/eventfd.h>
#endif
#ifdef PROXY
#include "proto_proxy.h"
#endif
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <netinet/tcp.h>

#include "queue.h"
#include "tls.h"
#include "../../libupcall/upcall.h"

#ifdef __sun
#include <atomic.h>
#endif

#define ITEMS_PER_ALLOC 64

__thread LIBEVENT_THREAD *worker_me = NULL;


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

/*
 * Each libevent instance has a wakeup pipe, which other threads
 * can use to signal that they've put a new connection on its queue.
 */
static LIBEVENT_THREAD *threads;

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

/* Must not be called with any deeper locks held */
void pause_threads(enum pause_thread_types type) {
    bool pause_workers = false;

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
            pause_workers = true;
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

    /* Only send a message if we have one. */
    if (!pause_workers) {
        return;
    }

    // TODO: implement worker pause signal for upcall model
}

// MUST not be called with any deeper locks held
// MUST be called only by parent thread
// Note: listener thread is the "main" event base, which has exited its
// loop in order to call this function.
void stop_threads(void) {
    int i;

    // assoc can call pause_threads(), so we have to stop it first.
    stop_assoc_maintenance_thread();
    if (settings.verbose > 0)
        fprintf(stderr, "stopped assoc\n");

    if (settings.verbose > 0)
        fprintf(stderr, "asking workers to stop\n");

    // TODO: implement worker stop signal for upcall model

    // All of the workers are hung but haven't done cleanup yet.

    if (settings.verbose > 0)
        fprintf(stderr, "asking background threads to stop\n");

    // stop each side thread.
    // TODO: Verify these all work if the threads are already stopped
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

    // Close all connections then let the workers finally exit.
    if (settings.verbose > 0)
        fprintf(stderr, "closing connections\n");
    conn_close_all();
    if (settings.verbose > 0)
        fprintf(stderr, "reaping worker threads\n");
    for (i = 0; i < settings.num_threads; i++) {
        pthread_join(threads[i].thread_id, NULL);
    }

    if (settings.verbose > 0)
        fprintf(stderr, "all background threads stopped\n");

    // At this point, every background thread must be stopped.
}

/*
 * Sets whether or not we accept new connections.
 */
void accept_new_conns(const bool do_accept) {
    pthread_mutex_lock(&conn_lock);
    do_accept_new_conns(do_accept);
    pthread_mutex_unlock(&conn_lock);
}
// Syscalls can be expensive enough that handling a few of them once here can
// save both throughput and overall latency.
#define MAX_PIPE_EVENTS 32


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

/********************************* WORKER SETUP ******************************/

static void accept_handler(struct up_event *evt);

static int worker_udp_listen(const char *interface, int port) {
    struct addrinfo hints = {
        .ai_flags    = AI_PASSIVE,
        .ai_family   = AF_UNSPEC,
        .ai_socktype = SOCK_DGRAM,
    };
    struct addrinfo *ai, *next;
    char port_buf[NI_MAXSERV];
    int flags = 1, error, sfd, success = 0;

    snprintf(port_buf, sizeof(port_buf), "%d", port);
    error = getaddrinfo(interface, port_buf, &hints, &ai);
    if (error != 0) {
        fprintf(stderr, "getaddrinfo(): %s\n", gai_strerror(error));
        return 1;
    }

    for (next = ai; next; next = next->ai_next) {
        sfd = socket(next->ai_family,
                     next->ai_socktype | SOCK_NONBLOCK | SOCK_CLOEXEC,
                     next->ai_protocol);
        if (sfd == -1) continue;

        setsockopt(sfd, SOL_SOCKET, SO_REUSEPORT, &flags, sizeof(flags));
        setsockopt(sfd, SOL_SOCKET, SO_REUSEADDR, &flags, sizeof(flags));

        if (bind(sfd, next->ai_addr, next->ai_addrlen) == -1) {
            close(sfd);
            continue;
        }

        conn *c = conn_new(sfd, conn_read, READ_BUFFER_SIZE,
                           udp_transport, NULL, 0, settings.binding_protocol);
        if (c == NULL) {
            close(sfd);
            continue;
        }
        add_read(sfd, udp_read_handler);
        success++;
    }
    freeaddrinfo(ai);
    return success == 0 ? 1 : 0;
}

static int worker_listen(const char *interface, int port) {
    struct addrinfo hints = {
        .ai_flags    = AI_PASSIVE,
        .ai_family   = AF_UNSPEC,
        .ai_socktype = SOCK_STREAM,
    };
    struct addrinfo *ai, *next;
    char port_buf[NI_MAXSERV];
    int flags = 1, error, sfd, success = 0;

    snprintf(port_buf, sizeof(port_buf), "%d", port);
    error = getaddrinfo(interface, port_buf, &hints, &ai);
    if (error != 0) {
        fprintf(stderr, "getaddrinfo(): %s\n", gai_strerror(error));
        return 1;
    }

    for (next = ai; next; next = next->ai_next) {
        sfd = socket(next->ai_family,
                     next->ai_socktype | SOCK_NONBLOCK | SOCK_CLOEXEC,
                     next->ai_protocol);
        if (sfd == -1) continue;

        setsockopt(sfd, SOL_SOCKET,  SO_REUSEPORT, &flags, sizeof(flags));
        setsockopt(sfd, SOL_SOCKET,  SO_REUSEADDR, &flags, sizeof(flags));
        setsockopt(sfd, SOL_SOCKET,  SO_KEEPALIVE, &flags, sizeof(flags));
        setsockopt(sfd, IPPROTO_TCP, TCP_NODELAY,  &flags, sizeof(flags));

        if (bind(sfd, next->ai_addr, next->ai_addrlen) == -1) {
            close(sfd);
            continue;
        }
        if (listen(sfd, settings.backlog) == -1) {
            close(sfd);
            continue;
        }
        success++;
        add_accept(sfd, accept_handler);
    }
    freeaddrinfo(ai);
    return success == 0 ? 1 : 0;
}

/* Parse one token from settings.inter into a host string and port.
 * Handles: [ipv6]:port, host:port, host, *.
 * Modifies p in-place.  Sets *host_out to NULL for wildcard/empty. */
static void parse_inter_token(char *p, int default_port,
                               char **host_out, int *port_out) {
    int32_t port = default_port;
    char *host = p;

    if (*p == '[') {
        char *e = strchr(p, ']');
        if (e != NULL) {
            host = p + 1;
            *e = '\0';
            if (*(e + 1) == ':')
                safe_strtol(e + 2, &port);
        }
    } else {
        char *s = strchr(p, ':');
        if (s != NULL && strchr(s + 1, ':') == NULL) {
            *s = '\0';
            safe_strtol(s + 1, &port);
        }
    }

    *host_out = (*host == '\0' || strcmp(host, "*") == 0) ? NULL : host;
    *port_out = (int)port;
}

static void worker_init_listeners(void) {
    if (settings.port) {
        if (settings.inter == NULL) {
            if (worker_listen(NULL, settings.port) != 0) {
                fprintf(stderr, "failed to listen on port %d\n", settings.port);
                exit(EXIT_FAILURE);
            }
        } else {
            char *list = strdup(settings.inter);
            char *b, *p;
            if (list == NULL) {
                perror("strdup");
                exit(EXIT_FAILURE);
            }
            for (p = strtok_r(list, ";,", &b); p; p = strtok_r(NULL, ";,", &b)) {
                char *host; int port;
                parse_inter_token(p, settings.port, &host, &port);
                if (worker_listen(host, port) != 0) {
                    fprintf(stderr, "failed to listen on %s:%d\n",
                            host ? host : "*", port);
                    exit(EXIT_FAILURE);
                }
            }
            free(list);
        }
    }
    // TODO: unix socket listener
    if (settings.udpport) {
        if (settings.inter == NULL) {
            if (worker_udp_listen(NULL, settings.udpport) != 0) {
                fprintf(stderr, "failed to listen on UDP port %d\n", settings.udpport);
                exit(EXIT_FAILURE);
            }
        } else {
            char *list = strdup(settings.inter);
            char *b, *p;
            if (list == NULL) {
                perror("strdup");
                exit(EXIT_FAILURE);
            }
            for (p = strtok_r(list, ";,", &b); p; p = strtok_r(NULL, ";,", &b)) {
                char *host; int port;
                parse_inter_token(p, settings.udpport, &host, &port);
                if (worker_udp_listen(host, port) != 0) {
                    fprintf(stderr, "failed to listen on UDP %s:%d\n",
                            host ? host : "*", port);
                    exit(EXIT_FAILURE);
                }
            }
            free(list);
        }
    }
}

static void accept_handler(struct up_event *evt) {
    int newfd = evt->result;

    add_accept(evt->fd, accept_handler);

    if (newfd < 0) {
        if (settings.verbose > 0)
            fprintf(stderr, "accept failed: %d\n", -newfd);
        return;
    }

    conn *c = conn_new(newfd, conn_new_cmd, 0, tcp_transport, NULL, 0,
                       settings.binding_protocol);
    if (c == NULL) {
        close(newfd);
        return;
    }
    add_read(newfd, read_handler);
}

static void worker_setup(int worker_id, int nr_workers) {
    LIBEVENT_THREAD *me = &threads[worker_id];
    worker_me = me;
    me->thread_id = pthread_self();

    if (pthread_mutex_init(&me->stats.mutex, NULL) != 0) {
        perror("Failed to initialize mutex");
        exit(EXIT_FAILURE);
    }

    me->rbuf_cache = cache_create("rbuf", READ_BUFFER_SIZE, sizeof(char *));
    if (me->rbuf_cache == NULL) {
        fprintf(stderr, "Failed to create read buffer cache\n");
        exit(EXIT_FAILURE);
    }
    if (settings.read_buf_mem_limit) {
        int limit = settings.read_buf_mem_limit / nr_workers;
        if (limit < READ_BUFFER_SIZE)
            limit = 1;
        else
            limit = limit / READ_BUFFER_SIZE;
        cache_set_limit(me->rbuf_cache, limit);
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
#ifdef PROXY
    if (settings.proxy_enabled) {
        proxy_thread_init(settings.proxy_ctx, me);
    }
#endif

    me->l = logger_create();
    me->lru_bump_buf = item_lru_bump_buf_create();
    if (me->l == NULL || me->lru_bump_buf == NULL) {
        abort();
    }

    if (settings.drop_privileges) {
        drop_worker_privileges();
    }

    worker_init_listeners();
}

#ifdef PROXY
static void worker_loop(void) {
    LIBEVENT_THREAD *me = &threads[upcall_worker_id()];
    if (me->proxy_ctx) {
        proxy_gc_poke(me);
    }
}
#define WORKER_LOOP worker_loop
#else
#define WORKER_LOOP NULL
#endif

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

    nthreads = upcall_nr_workers();

    for (i = 0; i < POWER_LARGEST; i++) {
        pthread_mutex_init(&lru_locks[i], NULL);
    }
    pthread_mutex_init(&worker_hang_lock, NULL);

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
    if (!item_locks) {
        perror("Can't allocate item locks");
        exit(1);
    }
    for (i = 0; i < item_lock_count; i++) {
        pthread_mutex_init(&item_locks[i], NULL);
    }

    threads = calloc(nthreads, sizeof(LIBEVENT_THREAD));
    if (!threads) {
        perror("Can't allocate thread descriptors");
        exit(1);
    }

    for (i = 0; i < nthreads; i++) {
#ifdef EXTSTORE
        threads[i].storage = arg;
#endif
        threads[i].thread_baseid = i;
    }

    if (upcall_init(64, 4096, worker_setup, WORKER_LOOP) != 0) {
        fprintf(stderr, "upcall_init failed\n");
        exit(EXIT_FAILURE);
    }
}

