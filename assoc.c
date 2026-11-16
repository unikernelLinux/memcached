/* -*- Mode: C; tab-width: 4; c-basic-offset: 4; indent-tabs-mode: nil -*- */
/*
 * Hash table: one 64-byte bucket per index. A bucket holds BUCKET_SLOTS
 * tagged item pointers and one overflow chain head. A lookup touches the
 * bucket line, compares the 16-bit tags in registers, and dereferences
 * only items whose tag matches, so the common hit costs one bucket miss
 * plus one item miss. Items that do not fit in a slot are chained from
 * the overflow pointer through it->h_next, as the old table did for all
 * items.
 *
 * The hash function used here is by Bob Jenkins, 1996:
 *    <http://burtleburtle.net/bob/hash/doobs.html>
 *       "By Bob Jenkins, 1996.  bob_jenkins@burtleburtle.net.
 *       You may use this code any way you wish, private, educational,
 *       or commercial.  It's free."
 *
 * The rest of the file is licensed under the BSD license.  See LICENSE.
 */

#include "memcached.h"
#include <sys/stat.h>
#include <sys/socket.h>
#include <sys/resource.h>
#include <sys/mman.h>
#include <signal.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <errno.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <pthread.h>

static pthread_cond_t maintenance_cond = PTHREAD_COND_INITIALIZER;
static pthread_mutex_t maintenance_lock = PTHREAD_MUTEX_INITIALIZER;

/* how many powers of 2's worth of buckets we use */
unsigned int hashpower = HASHPOWER_DEFAULT;

#define hashsize(n) ((uint64_t)1<<(n))
#define hashmask(n) (hashsize(n)-1)

#define BUCKET_SLOTS 7

/* A slot is a user-space pointer (47 significant bits) in the low 48 bits
 * and the tag in the high 16. Zero means empty, since no item is at 0. */
#define SLOT_PTR_MASK (((uint64_t)1 << 48) - 1)
#define slot_item(s) ((item *)(uintptr_t)((s) & SLOT_PTR_MASK))
#define slot_tag(s) ((uint16_t)((s) >> 48))
#define make_slot(it, tag) (((uint64_t)(uintptr_t)(it)) | ((uint64_t)(tag) << 48))

/* The bucket index is the low hashpower bits of the 32-bit hv, so the tag
 * is taken from the top. Above hashpower 16 the two overlap and the tag
 * loses one bit of discrimination per extra power. */
#define hv_tag(hv) ((uint16_t)((hv) >> 16))

typedef struct {
    uint64_t slot[BUCKET_SLOTS];
    /* Chain head for items past the slots. The high 16 bits of this
     * pointer are free for a per-bucket version counter later. */
    item *overflow;
} __attribute__((aligned(64))) bucket;

_Static_assert(sizeof(bucket) == 64, "bucket must be one cache line");

/* Main hash table. This is where we look except during expansion. */
static bucket *primary_hashtable = 0;

/*
 * Previous hash table. During expansion, we look here for keys that haven't
 * been moved over to the primary yet.
 */
static bucket *old_hashtable = 0;

/* Flag: Are we in the middle of expanding now? */
static bool expanding = false;

/*
 * During expansion we migrate values with bucket granularity; this is how
 * far we've gotten so far. Ranges from 0 .. hashsize(hashpower - 1) - 1.
 */
static uint64_t expand_bucket = 0;

/* Set by -L: the table comes from the same hugetlb pool as the slab arena. */
static bool table_hugetlb = false;

static size_t table_len(uint64_t nbuckets) {
    size_t len = nbuckets * sizeof(bucket);
#ifdef MAP_HUGETLB
    if (table_hugetlb) {
        size_t ps = hugepage_size();
        len = (len + ps - 1) & ~(ps - 1);
    }
#endif
    return len;
}

/* mmap gives zeroed, page-aligned memory; calloc does not promise the
 * 64-byte alignment the bucket layout needs. */
static bucket *table_alloc(uint64_t nbuckets) {
    int flags = MAP_PRIVATE | MAP_ANONYMOUS;
#ifdef MAP_HUGETLB
    if (table_hugetlb) {
        if (hugepage_size() == 0) {
            fprintf(stderr, "Failed to get the huge page size for the hash table\n");
            return NULL;
        }
        flags |= MAP_HUGETLB;
    }
#endif
    void *p = mmap(NULL, table_len(nbuckets), PROT_READ | PROT_WRITE, flags, -1, 0);
    if (p == MAP_FAILED) {
        fprintf(stderr, "Failed to mmap %zu bytes for the hash table: %s\n",
                table_len(nbuckets), strerror(errno));
        return NULL;
    }
    return p;
}

static void table_free(bucket *t, uint64_t nbuckets) {
    munmap(t, table_len(nbuckets));
}

void assoc_init(const int hashtable_init, const bool large_pages) {
    if (hashtable_init) {
        hashpower = hashtable_init;
    }
    table_hugetlb = large_pages;
    primary_hashtable = table_alloc(hashsize(hashpower));
    if (! primary_hashtable) {
        fprintf(stderr, "Failed to init hashtable.\n");
        exit(EXIT_FAILURE);
    }
    STATS_LOCK();
    stats_state.hash_power_level = hashpower;
    stats_state.hash_bytes = hashsize(hashpower) * sizeof(bucket);
    STATS_UNLOCK();
}

static inline bucket *bucket_for(const uint32_t hv) {
    uint64_t oldbucket;

    if (expanding &&
        (oldbucket = (hv & hashmask(hashpower - 1))) >= expand_bucket)
    {
        return &old_hashtable[oldbucket];
    }
    return &primary_hashtable[hv & hashmask(hashpower)];
}

static inline bool key_eq(const item *it, const char *key, const size_t nkey) {
    return nkey == it->nkey && memcmp(key, ITEM_key(it), nkey) == 0;
}

item *assoc_find(const char *key, const size_t nkey, const uint32_t hv) {
    bucket *b = bucket_for(hv);
    const uint16_t tag = hv_tag(hv);
    item *it;
#ifdef ENABLE_DTRACE
    int depth = 0;
#endif

    for (int i = 0; i < BUCKET_SLOTS; i++) {
        uint64_t s = b->slot[i];
        if (s != 0 && slot_tag(s) == tag) {
            it = slot_item(s);
            if (key_eq(it, key, nkey)) {
                MEMCACHED_ASSOC_FIND(key, nkey, 0);
                return it;
            }
        }
    }
    for (it = b->overflow; it != NULL; it = it->h_next) {
#ifdef ENABLE_DTRACE
        ++depth;
#endif
        if (key_eq(it, key, nkey)) {
            MEMCACHED_ASSOC_FIND(key, nkey, depth);
            return it;
        }
    }
    MEMCACHED_ASSOC_FIND(key, nkey, depth);
    return NULL;
}

static void bucket_insert(bucket *b, item *it, const uint32_t hv) {
    for (int i = 0; i < BUCKET_SLOTS; i++) {
        if (b->slot[i] == 0) {
            b->slot[i] = make_slot(it, hv_tag(hv));
            return;
        }
    }
    it->h_next = b->overflow;
    b->overflow = it;
}

/* grows the hashtable to the next power of 2. */
static void assoc_expand(void) {
    old_hashtable = primary_hashtable;

    primary_hashtable = table_alloc(hashsize(hashpower + 1));
    if (primary_hashtable) {
        if (settings.verbose > 1)
            fprintf(stderr, "Hash table expansion starting\n");
        hashpower++;
        expanding = true;
        expand_bucket = 0;
        STATS_LOCK();
        stats_state.hash_power_level = hashpower;
        stats_state.hash_bytes += hashsize(hashpower) * sizeof(bucket);
        stats_state.hash_is_expanding = true;
        STATS_UNLOCK();
    } else {
        primary_hashtable = old_hashtable;
        /* Bad news, but we can keep running. */
    }
}

void assoc_start_expand(uint64_t curr_items) {
    if (pthread_mutex_trylock(&maintenance_lock) == 0) {
        if (curr_items > (hashsize(hashpower) * 3) / 2 && hashpower < HASHPOWER_MAX) {
            pthread_cond_signal(&maintenance_cond);
        }
        pthread_mutex_unlock(&maintenance_lock);
    }
}

/* Note: this isn't an assoc_update.  The key must not already exist to call this */
int assoc_insert(item *it, const uint32_t hv) {
//    assert(assoc_find(ITEM_key(it), it->nkey) == 0);  /* shouldn't have duplicately named things defined */

    bucket_insert(bucket_for(hv), it, hv);

    MEMCACHED_ASSOC_INSERT(ITEM_key(it), it->nkey);
    return 1;
}

void assoc_delete(const char *key, const size_t nkey, const uint32_t hv) {
    bucket *b = bucket_for(hv);
    const uint16_t tag = hv_tag(hv);

    for (int i = 0; i < BUCKET_SLOTS; i++) {
        uint64_t s = b->slot[i];
        if (s != 0 && slot_tag(s) == tag && key_eq(slot_item(s), key, nkey)) {
            MEMCACHED_ASSOC_DELETE(key, nkey);
            b->slot[i] = 0;
            /* Refill the slot from the chain so chains only exist while
             * the bucket is full. The chain head's tag is recomputed. */
            item *o = b->overflow;
            if (o != NULL) {
                b->overflow = o->h_next;
                o->h_next = 0;
                b->slot[i] = make_slot(o, hv_tag(hash(ITEM_key(o), o->nkey)));
            }
            return;
        }
    }

    item **before = &b->overflow;
    while (*before && !key_eq(*before, key, nkey)) {
        before = &(*before)->h_next;
    }
    if (*before) {
        item *nxt;
        /* The DTrace probe cannot be triggered as the last instruction
         * due to possible tail-optimization by the compiler
         */
        MEMCACHED_ASSOC_DELETE(key, nkey);
        nxt = (*before)->h_next;
        (*before)->h_next = 0;   /* probably pointless, but whatever. */
        *before = nxt;
        return;
    }
    /* Note:  we never actually get here.  the callers don't delete things
       they can't find. */
    assert(*before != 0);
}


static volatile int do_run_maintenance_thread = 1;

#define DEFAULT_HASH_BULK_MOVE 1
int hash_bulk_move = DEFAULT_HASH_BULK_MOVE;

static void move_to_primary(item *it) {
    uint32_t hv = hash(ITEM_key(it), it->nkey);
    it->h_next = 0;
    bucket_insert(&primary_hashtable[hv & hashmask(hashpower)], it, hv);
}

static void *assoc_maintenance_thread(void *arg) {

    mutex_lock(&maintenance_lock);
    while (do_run_maintenance_thread) {
        int ii = 0;

        /* There is only one expansion thread, so no need to global lock. */
        for (ii = 0; ii < hash_bulk_move && expanding; ++ii) {
            item *it, *next;
            void *item_lock = NULL;

            /* bucket = hv & hashmask(hashpower) =>the bucket of hash table
             * is the lowest N bits of the hv, and the bucket of item_locks is
             *  also the lowest M bits of hv, and N is greater than M.
             *  So we can process expanding with only one item_lock. cool! */
            if ((item_lock = item_trylock(expand_bucket))) {
                    bucket *b = &old_hashtable[expand_bucket];
                    for (int i = 0; i < BUCKET_SLOTS; i++) {
                        if (b->slot[i] != 0) {
                            move_to_primary(slot_item(b->slot[i]));
                        }
                    }
                    for (it = b->overflow; NULL != it; it = next) {
                        next = it->h_next;
                        move_to_primary(it);
                    }
                    memset(b, 0, sizeof(*b));

                    expand_bucket++;
                    if (expand_bucket == hashsize(hashpower - 1)) {
                        expanding = false;
                        table_free(old_hashtable, hashsize(hashpower - 1));
                        STATS_LOCK();
                        stats_state.hash_bytes -= hashsize(hashpower - 1) * sizeof(bucket);
                        stats_state.hash_is_expanding = false;
                        STATS_UNLOCK();
                        if (settings.verbose > 1)
                            fprintf(stderr, "Hash table expansion done\n");
                    }

            } else {
                usleep(10*1000 - 1);
            }

            if (item_lock) {
                item_trylock_unlock(item_lock);
                item_lock = NULL;
            }
        }

        if (!expanding) {
            /* We are done expanding.. just wait for next invocation */
            pthread_cond_wait(&maintenance_cond, &maintenance_lock);
            /* assoc_expand() swaps out the hash table entirely, so we need
             * all threads to not hold any references related to the hash
             * table while this happens.
             * This is instead of a more complex, possibly slower algorithm to
             * allow dynamic hash table expansion without causing significant
             * wait times.
             */
            if (do_run_maintenance_thread) {
                pause_threads(PAUSE_ALL_THREADS);
                assoc_expand();
                pause_threads(RESUME_ALL_THREADS);
            }
        }
    }
    mutex_unlock(&maintenance_lock);
    return NULL;
}

static pthread_t maintenance_tid;

int start_assoc_maintenance_thread(void) {
    int ret;
    char *env = getenv("MEMCACHED_HASH_BULK_MOVE");
    if (env != NULL) {
        hash_bulk_move = atoi(env);
        if (hash_bulk_move == 0) {
            hash_bulk_move = DEFAULT_HASH_BULK_MOVE;
        }
    }

    if ((ret = pthread_create(&maintenance_tid, NULL,
                              assoc_maintenance_thread, NULL)) != 0) {
        fprintf(stderr, "Can't create thread: %s\n", strerror(ret));
        return -1;
    }
    thread_setname(maintenance_tid, "mc-assocmaint");
    return 0;
}

void stop_assoc_maintenance_thread(void) {
    mutex_lock(&maintenance_lock);
    do_run_maintenance_thread = 0;
    pthread_cond_signal(&maintenance_cond);
    mutex_unlock(&maintenance_lock);

    /* Wait for the maintenance thread to stop */
    pthread_join(maintenance_tid, NULL);
}

struct assoc_iterator {
    uint64_t bucket;
    int slot;       /* next slot to visit; BUCKET_SLOTS means the chain */
    item *next;     /* next chain item once the slots are done */
    bool bucket_locked;
};

void *assoc_get_iterator(void) {
    struct assoc_iterator *iter = calloc(1, sizeof(struct assoc_iterator));
    if (iter == NULL) {
        return NULL;
    }
    // this will hang the caller while a hash table expansion is running.
    if (mutex_trylock(&maintenance_lock) == 0) {
        return iter;
    } else {
        free(iter);
        return NULL;
    }
}

/* Visits the slots, then the chain, of each bucket under its item lock.
 * Returns true with *it == NULL when it steps to the next bucket. A
 * delete during the walk may refill a slot already passed; that item is
 * then skipped. */
bool assoc_iterate(void *iterp, item **it) {
    struct assoc_iterator *iter = (struct assoc_iterator *) iterp;
    *it = NULL;

    if (!iter->bucket_locked) {
        if (iter->bucket == hashsize(hashpower)) {
            return false;
        }
        // - only check the primary hash table since expand is blocked.
        item_lock(iter->bucket);
        iter->bucket_locked = true;
        iter->slot = 0;
    }

    bucket *b = &primary_hashtable[iter->bucket];
    while (iter->slot < BUCKET_SLOTS) {
        uint64_t s = b->slot[iter->slot++];
        if (s != 0) {
            *it = slot_item(s);
            return true;
        }
        if (iter->slot == BUCKET_SLOTS) {
            iter->next = b->overflow;
        }
    }
    if (iter->next != NULL) {
        *it = iter->next;
        iter->next = iter->next->h_next;
        return true;
    }

    item_unlock(iter->bucket);
    iter->bucket_locked = false;
    iter->bucket++;
    return true;
}

void assoc_iterate_final(void *iterp) {
    struct assoc_iterator *iter = (struct assoc_iterator *) iterp;
    if (iter->bucket_locked) {
        item_unlock(iter->bucket);
    }
    mutex_unlock(&maintenance_lock);
    free(iter);
}
