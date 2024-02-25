/*----------------------------------------------------------------------------
 * Generate CNF (conjunctive normal form) input for SAT solvers for
 * scheduling and packing problems.
 *
 * Author: Visegrady, Tamas <tamas.visegrady@gmail.com>
 *----------------------------------------------------------------------------
 */

// search for SIZE NOTE where assumptions are made

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>            // temporary; sqrt() only

#undef   SYS_NO_LMDB
#define  SYS_NO_LMDB  1  /* workaround: needs rest of transaction/logic */

#include <hiredis/hiredis.h>
#include <hiredis/read.h>

#define  USE_READINT
#define  USE_ERR_ANNOTATE
#define  USE_HEXDUMP    -1   /* no wrapping */
#include "common-util.h"

typedef enum {
	HSH_MAINHASH = 1,   /* primary/main variables */
	HSH_ADDLHASH = 2,   /* implicit, indirect variables */
} RdHash_t ;
/**/
#define  HSH_MAINHASH_NAME     "vars"
#define  HSH_MAINHASH_NBYTES   ((size_t) 4)
#define  HSH_ADDLHASH_NAME     "addl"
#define  HSH_ADDLHASH_NBYTES   ((size_t) 4)
/*
 * for hashtables which are mapped to files:
 */
#define  HSH_FS_HASHDIR          "/tmp/"
#define  HSH_FS_MAINHASH_FILE    HSH_FS_HASHDIR  "pnrmain.bin"
#define  HSH_FS_ADDLHASH_FILE    HSH_FS_HASHDIR  "pnraddl.bin"
/**/
#define  HSH_FS_FQNAME_MAX_BYTES  128

#define  HSH_READONLY  1

/* temp. variable names are '...operation(ID)...' '...addl-variable count...'
 * define limits for both, excluding any terminating \0
 */
#define  SAT_ID_MAX_BYTES  ((size_t) 8)  /* operation/ID limit */
#define  SAT_NR_MAX_BYTES  ((size_t) 8)

typedef enum {
	SAT_FL_INVERT     = 1,  // OR -> NOR, AND -> NAND etc.
	SAT_FL_ADD_VAR    = 2,  // add clause forcing the aggregate variable
	SAT_FL_ADD_NEGVAR = 4   // add clause forcing negated aggregate...
} SAT_Flag_t ;
//
#define SAT_FL_MASK  0x07

#define  SAT_CLAUSES_ENOUGH_BYTES  ((unsigned int) 1024)
#define  SAT_TEMPLTABLE_HDR_UNITS  ((unsigned int) 4)  // per-table header
#define  SAT_TEMPLHDR_UNITS  ((unsigned int) 4)  // per-template header

#define  SAT_SIZET_INVD      ((size_t) -1)
#define  SAT_SIZET_ENOMEM    ((size_t) -2)   // out of memory
#define  SAT_SIZET_ECOUNT    ((size_t) -3)   // invalid nr. of inputs
#define  SAT_SIZET_EINTERN   ((size_t) -4)   // (const) tables are inconsistent
#define  SAT_SIZET_EOUTPUTS  ((size_t) -5)   // inconsistent output definitions
#define  SAT_SIZET_ETOOSMALL ((size_t) -6)   // insufficient result buffer
// update valid_sat_size() if adding something here

#define  SAT_UINT_INVD       (~((unsigned int) 0))
// TODO: specific error-to-size_t mappings

// shared scratch used by examples
static unsigned char scratch[ 1024 *1024 ];

// recurring pair: array + nr. of elements
#define  ARRAY_OF(_arr)  _arr, ARRAY_ELEMS(_arr)

#include "imhash.h"

#if !defined(SYS_NO_LMDB)  /*=====  delimiter: LMDB access  ================*/
/* see www.lmdb.tech/doc/starting.html for API overview  [accessed 2023-04-14]
 *
 * these are core LMDB calls below, local instance only
 */
#include <errno.h>               /* LMDB passes through libc (POSIX) values */
#include <lmdb.h>

#if 0
//--------------------------------------
static inline
MDB_val *kvs__lmdb_data2mdb(MDB_val *pv, const void *data, size_t dbytes)
{
	if (pv) {
		pv->mv_data  = (void *) data;
		pv->mv_size  = dbytes;
	}

	return pv;
}


/*--------------------------------------
 * generic LMDB-to-KVS error mapping
 * SHOULD be called with error conditions only
 * includes libc err.codes as MDB may pass those through
 */
static int kvs__lmdberr2kvs(int rc)
{
	switch (rc) {
	case MDB_NOTFOUND: return KVS_ERR_NFOUND;

							// libc(POSIX) errors
	case ENOMEM:       return KVS_ERR_RESOURCE;

	default:
		break;
	}

	return rc;
}
#endif


/*--------------------------------------
 * opens a DB file, user-restricted, without creating any transactions
 */
static int lmd_open(MDB_env **env, MDB_dbi *dbi,
                              unsigned int mode, RdHash_t hash)
{
	const char *fname = NULL;
	int rc, flags = 0;

	if (!env || !dbi)
		return -1;
	*env = NULL;
	*dbi = 0;

	flags |= (HSH_READONLY & mode) ? MDB_RDONLY : MDB_WRITEMAP;

	switch (hash) {
	case HSH_MAINHASH:
		fname = HSH_FS_MAINHASH_FILE;
		break;

	case HSH_ADDLHASH:
		fname = HSH_FS_ADDLHASH_FILE;
		break;

	default:
		return -2;
	}

	rc = mdb_env_create(env);

	flags |= MDB_NOSYNC | MDB_NOSUBDIR;

	if (!rc) {
		rc = mdb_env_open(*env, fname, flags, 0600);
	}

	return rc ? -1 : 0;
}


#if 0
/*--------------------------------------
 * tolerates NULL DB etc., returning 'not found'
 * non-NULL 'val' and 0 'vbytes' writes empty data
 *
 * write transaction attached(nested) to 'txparent' if non-NULL
 */
static int kvs__lmdb_value2key(const unsigned char *key, size_t kbytes,
                               const unsigned char *val, size_t vbytes,
                                           MDB_env *env, MDB_dbi dbi,
                                           MDB_txn *txparent,
                                               int flags)
{
	MDB_txn *wr = NULL;
	int rc = 0;

	if (!key || !kbytes)
		return 0;

	rc = mdb_txn_begin(env, txparent, 0, &wr);
	if (rc)
		return rc;

	//-----  transaction open  -------------------------
	rc = mdb_open(wr, NULL, 0, &dbi);
	if (!rc) {
		MDB_val k, v;

		kvs__lmdb_data2mdb(&k, key, kbytes);
		kvs__lmdb_data2mdb(&v, val, vbytes);

		rc = mdb_put(wr, dbi, &k, &v, 0);
	}

	if (rc) {
		mdb_txn_abort(wr);
	} else {
	        rc = mdb_txn_commit(wr);
	}
	//-----  transaction closed  -----------------------

	MARK_UNUSED(flags);

	return (rc < 0) ? kvs__lmdberr2kvs(rc) : rc;
}


/*--------------------------------------
 * tolerates NULL env etc., returning 'not found'
 * read transaction attached(nested) to 'txparent' if non-NULL
 */
static int kvs__lmdb_key2value(unsigned char *val,  size_t vbytes,
                         const unsigned char *key,  size_t kbytes,
                                     MDB_env *env, MDB_dbi dbi,
                                     MDB_txn *txparent,
                                         int flags)
{
	MDB_txn *rd = NULL;
	int rc = 0;

	if (!key || !kbytes || !env)
		return KVS_ERR_TOOSMALL;

	rc = mdb_txn_begin(env, txparent, MDB_RDONLY, &rd);
	if (rc)
		return rc;

	//-----  transaction open  -------------------------
	do {
	MDB_val k, v;

	rc = mdb_open(rd, NULL, 0, &dbi);
	if (rc)
		break;

	kvs__lmdb_data2mdb(&k, key, kbytes);

	rc = mdb_get(rd, dbi, &k, &v);
	if (rc)
		break;

	if (!val) {
		rc = (long) v.mv_size;                            // size query

	} else if (vbytes < v.mv_size) {
		rc = KVS_ERR_TOOSMALL;

	} else {
		if (v.mv_size)
			memcpy(val, v.mv_data, v.mv_size);
		rc = (long) v.mv_size;
	}
	} while (0);
	mdb_txn_abort(rd);

	MARK_UNUSED(flags);

	return (rc < 0) ? kvs__lmdberr2kvs(rc) : rc;
}
#endif


/*--------------------------------------
 * do not expect failure when closing
 */
static int ldb_close(MDB_env **env, MDB_dbi *dbi)
{
	if (env && *env) {
		if (dbi) {
			mdb_close(*env, *dbi);
			*dbi = 0;
		}

		mdb_env_close(*env);
		*env = NULL;
	}

	return 0;
}


/*--------------------------------------
 * empty any existing 'hash' (main) or 'addl' tables
 * returns <0, >0 upon error/success, respectively
 */
static int lmd_hash0(MDB_env **env, MDB_dbi *dbi, RdHash_t hash)
{
	int rc;

	rc = lmd_open(env, dbi, 0, hash);

	if (!rc && dbi) {
		MDB_txn *clr = NULL;

		rc = mdb_txn_begin(*env, NULL, 0, &clr)  |
		     mdb_drop(clr, *dbi, 0 /*empty DB*/) |
		     mdb_txn_commit(clr);

		if (rc) {
			mdb_txn_abort(clr);
			rc = -1;
		}
	}

	return rc ? -1 : 1;
}

#endif   /*=====  /delimiter: LMDB access  =================================*/


#if !defined(SYS_NO_REDIS)  /*=====  delimiter: Redis access  ==============*/
#define  RD_DEFAULT_PORT  6379


//--------------------------------------
typedef enum {
	SAT_E_INTERNAL = -1,
	SAT_E_DB       = -2,
	SAT_E_DB_VALUE = -3   // unexpected data/type found in database
} SatErr_t ;


//--------------------------------------
static redisContext *rds_open(const char *hostname, int port)
{
	struct timeval timeout = { 1, 500000 };                      // 1.0 sec
	redisContext *ctx = NULL;

	if (!hostname)
		hostname = "localhost";

	if (!port)
		port = RD_DEFAULT_PORT;

	ctx = redisConnectWithTimeout(hostname, port, timeout);

	if (!ctx || ctx->err) {
		if (ctx) {
			printf("Connection error: %s\n", ctx->errstr);
			redisFree(ctx);
			ctx = NULL;
		} else {
			printf("Connection: redis context alloc fail\n");
		}
	}

	return ctx;
}


//--------------------------------------
static inline int rd_reply_is_type(const redisReply *reply, int type)
{
	return (reply && (reply->type == type));
}


//--------------------------------------
#define RD_REPLY_IS_INT(r)     rd_reply_is_type((r), REDIS_REPLY_INTEGER)
#define RD_REPLY_IS_STRING(r)  rd_reply_is_type((r), REDIS_REPLY_STRING)


//--------------------------------------
static inline size_t rds_hash2id(const char **name, RdHash_t hash)
{
	switch (hash) {
	case HSH_MAINHASH:
		if (name)
			*name = HSH_MAINHASH_NAME;
		return HSH_MAINHASH_NBYTES;

	case HSH_ADDLHASH:
		if (name)
			*name = HSH_ADDLHASH_NAME;
		return HSH_ADDLHASH_NBYTES;

	default:
		if (name)
			*name = NULL;
		return 0;
	}
}


/*--------------------------------------
 * empty the entire 'hash' table
 *
 *---  Redis:  --------
 *  DEL  ...table...
 */
static int rds_hash0(redisContext *ctx, RdHash_t hash)
{
	int rc =  0;

	if (ctx) {
		const char *db = NULL;
		size_t dbytes;

		dbytes = rds_hash2id(&db, hash);

		if (db && dbytes) {
			redisReply *reply = NULL;

			reply = redisCommand(ctx, "DEL %b", db, dbytes);
			rc    = RD_REPLY_IS_INT(reply) ? 1 : -1;

			freeReplyObject(reply);
		}
	}

	return rc;
}


/*--------------------------------------
 * register (str, sbytes) -> (value) into hashtable selected by (db, dbytes)
 * does not change existing assignment
 *
 * returns <0  if anything failed
 *
 * assigns (...nr. of elements..) +1 if 'value' is 0
 * caller MUST NOT update database while changing that way
 * with uint64, we do not care about counter wrapping
 *
 * note: successful hash/update operations return ints, so not
 * specifically checking for _REPLY_ERROR
 *
 *---  Redis:  --------
 *  HLEN    ...table...                  -- query hash element count
 *  HSETNX  ...table...  ...key...  ...value...
 *                                       -- sets key->value if key is
 *                                       -- not yet present
 */
static int rds_str2db1(redisContext *ctx, const char *str, size_t sbytes,
                                            uint64_t value,
                                            RdHash_t hash)
{
	redisReply *reply = NULL;
	int rc = 0;

	do {
	if (ctx && str) {
		const char *db = NULL;
		size_t dbytes;

		dbytes = rds_hash2id(&db, hash);
		if (!dbytes) {
			rc = SAT_E_INTERNAL;
			break;
		}

		if (!sbytes)
			sbytes = strlen(str);

		if (!value) {
			reply = redisCommand(ctx, "HLEN %b", db, dbytes);
			rc    = RD_REPLY_IS_INT(reply) ? 1 : SAT_E_DB;
			value = reply ? (reply->integer +1) : 0;

			freeReplyObject(reply);
			if (rc < 0)
				break;
		}

		reply = redisCommand(ctx, "HSETNX %b %b %u", db, dbytes,
		                     str, sbytes, value);

		rc = RD_REPLY_IS_INT(reply) ? (int) reply->integer : -1;

		freeReplyObject(reply);

		if (rc >= 0) {
			reply = redisCommand(ctx, "HSETNX %b %u %b",
					db, dbytes, value, str, sbytes, value);

			rc = RD_REPLY_IS_INT(reply) ? (int) reply->integer : -1;
		}
	}
	} while (0);

	freeReplyObject(reply);

	return rc;
}


/*--------------------------------------
 * register (str, sbytes) into main hashtable
 * assigns (...nr. of elements..) +1 if 'value' is 0
 *
 * 'what', at some point, may select if we need multiple string-to-int hashes
 */
static int rds_str2db_main(redisContext *ctx, const char *str, size_t sbytes,
                                                uint64_t value)
{
	return rds_str2db1(ctx, str, sbytes, value, HSH_MAINHASH);
}


/*--------------------------------------
 * retrieve table[str] from 'hash'
 * returns ~0 if not found, invalid hash ID etc.
 */
static uint64_t rds_lookup1(redisContext *ctx, const char *str, size_t sbytes,
                                                 RdHash_t hash)
{
	redisReply *reply = NULL;
	uint64_t rc = 0;

	do {
	if (ctx && str) {
		const char *db = NULL;
		size_t dbytes;

		dbytes = rds_hash2id(&db, hash);
		if (!dbytes) {
			rc = ~((uint64_t) 0);
			break;
		}

		if (!sbytes)
			sbytes = strlen(str);

		reply = redisCommand(ctx, "HGET %b %b", db, dbytes,
		                     str, sbytes);

					// hash flattened INTs to STRING
		rc = RD_REPLY_IS_STRING(reply)
		     ? cu_readuint(reply->str, 0)
		     : ~((uint64_t) 0);
	}
	} while (0);

	freeReplyObject(reply);

	return rc;
}


/*--------------------------------------
 * retrieve table[str] from 'hash'
 * returns ~0 if not found, invalid hash ID etc.
 */
static uint64_t rds_lookup_main(redisContext *ctx,
                                  const char *str, size_t sbytes)
{
	return rds_lookup1(ctx, str, sbytes, HSH_MAINHASH);
}
#endif   /*=====  !SYS_NO_REDIS  ===========================================*/


struct PNR_DB {
#if !defined(SYS_NO_REDIS)
	struct {
		redisContext *ctx;
	} rd ;
#endif

#if !defined(SYS_NO_LMDB)
	struct {
		MDB_env *henv;
		MDB_env *aenv;

		MDB_dbi hdbi;
		MDB_dbi adbi;
	} lm ;
#endif
} ;


/*--------------------------------------
 * releases everything related to DBs/backends
 * clears structure, but does not release it
 */
static struct PNR_DB *db_release(struct PNR_DB *db)
{
	if (db) {
#if !defined(SYS_NO_REDIS)
		redisFree(db->rd.ctx);
#endif

#if !defined(SYS_NO_LMDB)
		ldb_close(&( db->lm.henv ), &( db->lm.hdbi ));
		ldb_close(&( db->lm.aenv ), &( db->lm.adbi ));
#endif

		memset(db, 0, sizeof(*db));
	}

	return db;
}


#if 1   /*=====  delimiter: SAT converter  =================================*/
#define STC_VEC_SIGN_U64S    1     /* nr. of 64-bit bitvectors storing signs */
#define STC_CLS_MAX_ELEMS   (STC_VEC_SIGN_U64S * 64)
#define STC_NAME_MAX_BYTES  16
#define STC_NR_MAX_BYTES    12
#define STC_STR_MAX_BYTES  128   /* 'large enough' for any string we format */

#define STC_ADDL_UNITS  ((unsigned int) 40000)  /* grow arrays in such units */
#define STC_STR_UNITS   ((size_t) 1000000)    /* collated string growth size */

#define STC_REP_PREFIX         "SAT="
#define STC_REP_PREFIX_BYTES   ((size_t) 4)
#define STC_NEWNAME_PREFIX     "NV"
#define STC_NEWNAME_PFX_BYTES  2
#define STC_TEXTLN_MAX_BYTES   ((size_t) 1024)     // arbitrary; checked

typedef enum {
	STC_R_VSTRING      =     1,  // log string form of variable
	STC_R_VNUMBER      =     2,  // log variable number
	STC_R_EMBED        =     4,  // embed output; use STC_REP_PREFIX for
	                             // lines targeted to SAT solver
	STC_R_SATCOMMENT   =     8,  // target is for SAT comment region
	STC_R_NOFRAME      =  0x10,  // format clauses only, no other content
	STC_R_NOCOMMENT    =  0x20,  // exclude comment-only lines
	STC_R_VARLIST_ONLY =  0x40,  // variable-list only
	STC_R_CLAUSE_ONLY  =  0x80,  // clauses only (raw list)
	STC_R_NO_TAIL      = 0x100   // skip final, terminating newline
} SatReport_t ;


#if 2   /*=====  delimiter: SAT template-to-CNF converter (v2)  ============*/
#include "cnf-templates.h"
#include "cnf-lessthan-template.h"
#include "cnf-neq0-template.h"     // we do not actually use this non-forced
                                   // version for current schedules
#include "cnf-neq0forced-template.h"
#include "cnf-diff-template.h"
#include "cnf-1ofn-template.h"
#include "cnf-and-template.h"
#include "cnf-or-template.h"
#include "cnf-or1-template.h"
#endif

/*--------------------------------------
 * 'compact strings'
 * - offsets within concatenated arrays are uint32_t's
 * - max. net string length <= 255
 * - compact strings are uint64_t's which store <offset[32] || len[16]>
 *   - we may add special lengths etc., so 16 bits with currently <=8 used
 *   - MS 16 bits currently reserved-0
 * - 0 is invalid compact string (since we do not deal with empty strings)
 *
 * - limits:
 *   we assume size_t >= 32; on restricted platforms, if u32+u.char MAY
 *   wrap around size_t==32 bits, we do not care.
 */


struct SatClause {
	uint64_t neg[ STC_VEC_SIGN_U64S ];
		// entry #0 is (1 << 63), #1 is (1 << 62) of 1st entry etc.

		// offset+size into single shared concatenated-string
		//
	uint32_t soffset[ STC_CLS_MAX_ELEMS ];
	unsigned char sbytes[ STC_CLS_MAX_ELEMS ];

// TODO: once we increase length limit, it is prob. simpler to just store
// arrays of compact strings

		// != 0 if actual variable number is known
	int32_t varnr[ STC_CLS_MAX_ELEMS ];

	uint64_t comment;

	unsigned int used;
} ;
//
#define SAT_CLAUSE0  { {0,}, {0,}, {0,}, {0,}, 0, 0, }


struct SatName {
	unsigned char s[ STC_NAME_MAX_BYTES +1 ];
	size_t sbytes;

	uint64_t cs;     /* compact string, if known */

	unsigned int invert;   /* is the implied use inverted, below? */
} ;
//
#define SAT_NAME_INIT0  { {0,}, 0, 0, 0, }


// formatted line
struct SatFormat {
	unsigned char s[ STC_TEXTLN_MAX_BYTES +1 ];
	size_t sbytes;                // actually used, incl. any \0 terminator
} ;
//
#define SAT_FORMAT0  { {0,}, 0, }


// recurring index: nr. of elements allocated; actually used 
struct SatDynLimits {
	unsigned int allocd;
	unsigned int used;
} ;
//
#define SAT_DYNLIMITS_INIT0  { 0, 0, }


struct SatStrings {
	unsigned char *strs;
	size_t used;              // offset of first available byte
	size_t allocd;

// TODO: offset and size arrays
} ;
//
#define SAT_STRINGS0  { NULL, 0, 0, }


/*--------------------------------------
 * status update: report additional variables/clauses/etc. just added
 */
#define  SAT_MAX_RESULT_VARS  ((unsigned int) 1)

// TODO: merge with SAT_Summary (which no longer carries description)

struct SatAdded {
	uint32_t result[ SAT_MAX_RESULT_VARS ];   // results of added operation
	unsigned int rvars;

	unsigned int addvars;     // new (indirect) variables
	unsigned int clauses;     // new clauses
} ;
//
#define SAT_ADDED_INIT0  { { 0, }, 0, 0, 0, }


//--------------------------------------
struct SAT_Summary {
	unsigned int vars;
	unsigned int addl;
	unsigned int clauses;
	unsigned int maxcvars;
} ;
//
#define SAT_SUMMARY_INIT0 { 0, 0, 0, 0, }


//--------------------------------------
struct SatNumbers {
	int32_t *n;
	unsigned int allocd;
	unsigned int used;

	struct SatDynLimits limits;
} ;
//
#define SAT_NUMBERS_INIT0 { NULL, 0, 0, 0, SAT_DYNLIMITS_INIT0, }


//--------------------------------------
struct SatNrRefs {
	unsigned int *refs;         // (index) (nr.used) pairs, concatenated
	struct SatDynLimits limits;
} ;
//
#define SAT_NREFS_INIT0 { { 0, }, SAT_DYNLIMITS_INIT0, }


//--------------------------------------
struct SatState {
	struct PNR_DB db;

	struct SatStrings s;

	struct SatStrings comments;

	struct SatClause *c;
	unsigned int c_used;          // nr. of clauses already populated
	unsigned int c_allocd;

	struct SAT_Summary vinfo;   // TODO: collect everything here

	struct SatNumbers ns;       // clauses' numbers, expanded into int lists
	                            // .used includes clause-terminating 00's
	unsigned int n_used;        // net used: nr. of nonzero entries in .used
	unsigned int n_clauses;     // total number of numeric-clauses added

	struct SatNrRefs crefs;     // clause-references into integer list

	unsigned int vars;          // total nr. of variables added
	unsigned int addvars;       // number of additional, indirect etc.
	                            // variables
	unsigned int maxvaridx;     // maximum of any index seen so far
	unsigned int nzclauses;     // non-comment, non-empty clauses
} ;


/*--------------------------------------
 * recurring primitive: offset, entries in remaining part of SatNumbers
 */
static int32_t *sat_nrs_1st_unused(const struct SatNumbers *pn) ;
static int32_t *sat_nrs_1st_unused(const struct SatNumbers *pn) ;
//
#define  SAT_NR_UNUSED(pn)   sat_nrs_1st_unused(pn), sat_nrs_unused_count(pn)


/*--------------------------------------
 * wrapper struct; collection of related sub-structures
 * used by all template-to-... conversions
 */
struct SatConvert {
	struct SatAdded    add;   // values actually added
	struct SAT_Summary vars;  // read from template
	struct TemplIndex  ix;
} ;
/**/
#define SAT_CONVERT_INIT0  { SAT_ADDED_INIT0, SAT_SUMMARY_INIT0, \
                             CNF_TEMPLIDX_INIT0, }


// 32-bit IDs: store 4-bit prefix for type, 28-bit (packed) integer ID
//
// type(4):
//   x0     D/T/V    delivery, time unit, vehicle-ID bit
//   x1     D/T      delivery, time unit
//   x2     D/V      delivery, vehicle-ID bit
//   x8     aux. variable
//
// number ranges: D: 10000; T: 1000; V: 10
//     10k   deliveries
//     1000  time units =416 days at 10-minute resolution
//     10:   1000+ vehicles (2^10 bits to identify them)
//
// if we grow out of these limits, it will be time to move beyond 32-bit
// hashtables. the 32-bit form fits many nice embeddable ones (as of 2023-04)

static inline int is_valid_sat_size(size_t s) ;


#if 1   //-----  delimiter: streaming  ---------------------------------------
/*--------------------------------------
 * append (add, abytes) into (res+offs, rbytes-offs)
 * returns updated offset
 *
 * tolerates NULL 'res', which just marks increasing offsets for size queries
 * in that mode, NULL 'add' is also tolerated; only 'abytes' matters
 *
 * passes through error offsets etc., so safe to chain calls
 * opportunistically 0-terminates written buffer
 */
static size_t stream_append(void *res, size_t rbytes, size_t offs,
                      const void *add, size_t abytes)
{
	unsigned char *pr = (unsigned char *) res;

	if UNLIKELY(!is_valid_sat_size(offs))
		return offs;                              // error pass-through

	if UNLIKELY(!res && add)
		return SAT_SIZET_INVD;     // non-NULL res implies non-NULL add

	if UNLIKELY((offs > rbytes) || (offs + abytes > rbytes))
		return SAT_SIZET_ETOOSMALL;


	if (res && abytes)
		memmove(pr +offs, add, abytes);

	offs += abytes;

	if (offs < rbytes)
		pr[ offs ] = '\0';

	return offs;
}


/*--------------------------------------
 * tolerates special cases for written buffer/offset:
 *   - NULL pointer
 *   - offset indicating an error
 *
 * returns 'p' for error-related offsets
 */
static const void *ptr_with_offset(const void *p, size_t offset)
{
	const unsigned char *r = (const unsigned char *) p;

	return (p && is_valid_sat_size(offset)) ? (r + offset) : p;
}


/*--------------------------------------
 * remaining size for buffer with known offset
 * tolerates error-indicating offsets
 *
 * returns 0 for insufficient output, or error-related offsets
 */
static size_t size_with_offset(size_t rbytes, size_t offset)
{
	return (is_valid_sat_size(offset) && (offset < rbytes))
	        ? (rbytes -offset) : 0;
}


/*--------------------------------------
 * since we lack templates, here is a size-specialized typesafe 'max()'
 */
static inline unsigned int max_uint(unsigned int i, unsigned int j)
{
	return (i < j) ? j : i;
}

#endif   //-----  /delimiter: streaming  -------------------------------------


//--------------------------------------
static inline int is_valid_unsigned_int(unsigned int v)
{
	return (v != SAT_UINT_INVD);
}


//--------------------------------------
static inline int is_valid_sat_size(size_t s)
{
	switch (s) {
	case SAT_SIZET_INVD:
	case SAT_SIZET_ENOMEM:
	case SAT_SIZET_ECOUNT:
	case SAT_SIZET_EINTERN:
	case SAT_SIZET_ETOOSMALL:
	case SAT_SIZET_EOUTPUTS:
		return 0;

	default:
		return 1;
	}
}


//--------------------------------------
static inline struct SAT_Summary *sat_summary_init0(struct SAT_Summary *ps)
{
	if (ps)
		*ps = (struct SAT_Summary) SAT_SUMMARY_INIT0;

	return ps;
}


/*--------------------------------------
 * prefix-free mapping of auxiliary-variable number to 32-bit unique ID
 * see also sat_dtvvar2id()
 *
 * returns ~0 if value is out of range
 */
static inline uint32_t sat_auxvar2id(unsigned int varnr)
{
	return (varnr > 0x0fffffff)
	        ? (UINT32_C(0x80000000) | varnr)
	        : ~((uint32_t) 0);
}


/*--------------------------------------
 * number of clauses used
 *
 * returns 0 for uninitialized/NULL state
 */
static inline unsigned int sat_state2clausecnt(const struct SatState *ps)
{
	return (ps && ps->c && (ps->c_used < ps->c_allocd)) ? ps->c_used : 0;
}


/*--------------------------------------
 * encode some combination of 1-based delivery ID, 1-based time unit,
 * 1-based vehicle-bit ID into a 32-bit unique ID
 *
 * any 0 indicates the field is unused
 *
 * returns ~0 if any of the values is out of range
 */
static inline
uint32_t sat_var2id_core(unsigned int d, unsigned int t, unsigned int v)
{
	unsigned int dtv = ((!!d) << 16) | ((!!t) << 8) | !!v;
	uint32_t pack;

	if ((d && (d > 10000)) ||
	    (t && (t >  1000)) ||
	    (v && (v >    10)))
		return ~((uint32_t) 0);

//   x0     D/T/V    delivery, time unit, vehicle-ID bit
//   x1     D/T      delivery, time unit
//   x2     D/V      delivery, vehicle-ID bit

	pack =  d ? ((d-1) * 10000) : 0;
	pack += t ? ((t-1) * 10)    : 0;
	pack += v ?  (v-1)          : 0;

	switch (dtv) {
		case 0x10101:                         // D+T+V
			return UINT32_C(0x00000000) | pack;

		case 0x10100:                         // D+T
			return UINT32_C(0x10000000) | pack;

		case 0x10001:                         // D+V
			return UINT32_C(0x20000000) | pack;

		default:
			break;
	}

	return ~((uint32_t) 0);
}


/*--------------------------------------
 * D+T only: zero-based D+T
 */
static inline uint32_t sat_var2id_dt(unsigned int d, unsigned int t)
{
	return sat_var2id_core(d+1, t+1, 0);
}


/*--------------------------------------
 * D+V only: zero-based D+V
 */
static inline uint32_t sat_var2id_dv(unsigned int d, unsigned int v)
{
	return sat_var2id_core(d+1, 0, v+1);
}


/*--------------------------------------
 * D+V only: zero-based D+T+V
 */
static inline
uint32_t sat_var2id_dtv(unsigned int d, unsigned int t, unsigned int v)
{
	return sat_var2id_core(d+1, t+1, v+1);
}


//--------------------------------------
static inline struct SatClause *sat_clause_init0(struct SatClause *ps)
{
	if (ps)
		*ps = (struct SatClause) SAT_CLAUSE0;

	return ps;
}


//--------------------------------------
static inline struct SatName *sat_name_init0(struct SatName *pn)
{
	if (pn)
		*pn = (struct SatName) SAT_NAME_INIT0;

	return pn;
}


/*--------------------------------------
 * 0 is reported as invalid (or uninitialized/unused)
 */
static inline int is_valid_clauseelem_count(unsigned int n)
{
	return (n <= STC_CLS_MAX_ELEMS);
}


//--------------------------------------
static inline uint32_t cstring2offset(uint64_t s)
{
	return (uint32_t) (s >> 16);
}


/*--------------------------------------
 * adding offset2bytes() creates compact string representation
 */
static inline uint64_t offset2cstring(uint32_t offset)
{
	return ((uint64_t) offset) << 16;
}


//--------------------------------------
static inline size_t cstring2bytes(uint64_t s)
{
	return (unsigned char) s;
}


/*--------------------------------------
 * adding offset2cstring() creates compact string repr.
 * macro just present to mark size limits and make conversion explicit
 */
static inline unsigned char bytes2cstring(size_t bytes)
{
	return (unsigned char) bytes;
}


/*--------------------------------------
 * is the name unexpectedly empty, or too long?
 *
 * tolerates NULL, which is not always an invalid option
 */
static inline int is_invalid_name(const char *n, size_t nbytes)
{
	if (n && (!nbytes || (nbytes > STC_NAME_MAX_BYTES)))
		return 1;

	return 0;
}


/*--------------------------------------
 * opportunistic replication of name to other name field
 *
 * basically, our opportunistic strlcpy() equivalent/wrapper
 * with consistent NULL behaviour
 *
 * 'nbytes' is without \0-pad
 */
static inline void *sat_strcpy(void *r, size_t rbytes,
                         const char *n, size_t nbytes)
{
	if (r && n && (rbytes +1 > nbytes)) {
		unsigned char *pr = (unsigned char *) r;

		memmove(r, n, nbytes);
		pr[ nbytes ] = '\0';
	}

	return r;
}


/*--------------------------------------
 * return 1-based nr. of elements used (1 == present but unused)
 *        <0  if reference is NULL
 */
static int sat_entries_used(const void *ptr, const struct SatDynLimits *pd)
{
	return (ptr && pd) ? ((int) (pd->used +1)) : -1;
}


/*--------------------------------------
 * ensure at least 'n' unused entries are available
 * returns newly allocated/reallocated ptr, non-NULL, upon success
 *         NULL if reallocation fails, or anything inconsistent
 *
 * 'src' is NULL, or a previously returned ptr
 * call with n>0 to avoid undef. behaviour
 */
static void *sat_ensure_entries(struct SatDynLimits *pd,
                                         const void *src,
                                       unsigned int n, size_t unitbytes)
{
	void *r = NULL;

	do {                          // set r; break for any early termination
	if (unitbytes && pd) {
		unsigned int after = pd->allocd + STC_ADDL_UNITS;

		if (src && ((pd->used +n) <= pd->allocd)) {     // already fits
			r = (void *) src;
			break;
		}

		r = realloc((void *) src, after * unitbytes);
		if (r) {
			unsigned char *start = (unsigned char *) r +
				pd->used * unitbytes;
					// first address in newly added region
			
			memset(start, 0, (after - pd->used) * unitbytes);
				// there is no realloc() equivalent of calloc()

			pd->allocd = after;
		}
	}
	} while (0);

	return r;
}


/*--------------------------------------
 * at least 'n' unused number refs are available in 'ps'
 * returns 1-based index of first unused entry upon success
 *
 * reminder: these entries just stack
 */
static int sat_ensure_numrefs(struct SatState *ps, unsigned int n)
{
	if (ps) {
		if (!n)
			return 0;

// TODO: centralized check for .used <= .allocd etc
// TODO: centralized n<..max.limit.. etc. checks
		if (!ps->crefs.refs) {
			ps->crefs.refs = calloc(STC_ADDL_UNITS,
			                     sizeof(int32_t) * STC_ADDL_UNITS);
			if (!ps->crefs.refs)
				return -1;

			ps->ns.allocd = STC_ADDL_UNITS;
			ps->ns.used   = 0;
		}

		ps->crefs.refs = sat_ensure_entries(&( ps->crefs.limits ),
		                     ps->crefs.refs, n, sizeof(int32_t));

		return sat_entries_used(ps->crefs.refs, &( ps->crefs.limits ));
	}

	return -1;
}


/*--------------------------------------
 * at least 'n' unused numbers are available in 'ps'
 * returns 1-based index of first unused entry upon success
 */
static int sat_ensure_numbers(struct SatState *ps, unsigned int n)
{
	if (ps) {
		if (!n)
			return 0;

// TODO: centralized check for .used <= .allocd etc
// TODO: centralized n<..max.limit.. etc. checks
// TODO: centralized init-from-NULL
		if (!ps->ns.n) {
			ps->ns.n = calloc(STC_ADDL_UNITS,
			                  sizeof(int32_t) * STC_ADDL_UNITS);
			if (!ps->ns.n)
				return -1;
			ps->ns.allocd = STC_ADDL_UNITS;
			ps->ns.used   = 0;
		}

		ps->ns.n = sat_ensure_entries(&( ps->ns.limits ),
		                      ps->ns.n, n, sizeof(int32_t));

		return sat_entries_used(ps->ns.n, &( ps->ns.limits ));
	}

	return -1;
}


/*--------------------------------------
 * at least 'n' clauses are available in 'ps'
 */
static int sat_ensure_clauses(struct SatState *ps, unsigned int n)
{
	if (ps && n) {
// TODO: centralized check for .used <= .allocd etc
// TODO: centralized n<..max.limit.. etc. checks
		if (!ps->c) {
			ps->c = calloc(STC_ADDL_UNITS,
				sizeof(struct SatClause) * STC_ADDL_UNITS);
			if (!ps->c)
				return -1;
			ps->c_allocd = STC_ADDL_UNITS;
			ps->c_used   = 0;
		}

		if ((ps->c_used +n) > ps->c_allocd) {
			unsigned int after = ps->c_allocd + STC_ADDL_UNITS;
			ps->c = realloc(ps->c,
			                 after*sizeof(struct SatClause));
			if (!ps->c)
				return -2;
// TODO: add tmp pointer, even if we do not care about out-of-mem state

				// why is there no calloc()-equivalent realloc?
				// grrrr.
				//
				// TODO: exact range to set-0, in
				// separate/readable tmp.variable
				//
			memset(&(ps->c[ ps->c_used ]), 0, (after - ps->c_used)*
			                             sizeof(struct SatClause));

			ps->c_allocd = after;
		}

		return 0;
	}

	return -1;
}


//--------------------------------------
static inline
void sat_register_clauses(struct SatState *ps, unsigned int incr) ;


/*--------------------------------------
 * add place for +X clauses; X>0
 * returns ptr to clauses upon success
 * sets non-NULL 'idx' to index of first new entry
 */
static struct SatClause *sat_add_clauses(struct SatState *ps,
                                            unsigned int *idx,
                                            unsigned int add)
{
	if (idx)
		*idx = 0;     // ensure always initialized, even on error paths

	if (ps && add) {
		if (sat_ensure_clauses(ps, add) <0)
			return 0;

		if (idx)
			*idx = ps->c_used;

		sat_register_clauses(ps, add);

		return ps->c;
	}

	return NULL;
}


/*--------------------------------------
 * recurring pattern: multiple clauses, identical variables
 * structures' overlap is undefined
 *
 * note: replicates padding bytes from arrays (undefined); we do not care
 */
static void sat_clone_strings(struct SatClause *dst,
                        const struct SatClause *src)
{
	if (dst && src && ((const struct SatClause *) src != dst)) {
		memcpy(dst->soffset, src->soffset, sizeof(src->soffset));

		memcpy(dst->sbytes,  src->sbytes,  sizeof(src->sbytes));

		dst->used = src->used;
	}
}


#if 0
/*--------------------------------------
 * concat (a | b | c) with intervening+trailing \0 terminators to (res,rbytes)
 *
 * input strings are net, exclude \0 termination
 *
 * registers into [0..2] entries of SatClause, if non-NULL
 * does not update other entries
 *
 * TODO: protect against/document lack of int. overflows
 */
static size_t sat_string3x(unsigned char *res, size_t rb,
                        struct SatClause *pc,
                              const char *a,   size_t ab,
                              const char *b,   size_t bb,
                              const char *c,   size_t cb)
{
	if (res && a && b && c && ab && bb && cb) {
		if (rb < ((ab +bb +cb) +3))
			return 0;

		memmove(res,               a, ab);
		memmove(res +1 +ab,        b, bb);
		memmove(res +1 +ab +1 +bb, c, cb);

		res[ ab               ] = '\0';
		res[ ab +1 +bb        ] = '\0';
		res[ ab +1 +bb +1 +cb ] = '\0';

		if (pc) {
			pc->soffset[ 0 ] = 0;
			pc->soffset[ 1 ] = ab +1;
			pc->soffset[ 2 ] = ab +1 +bb +1;

			pc->sbytes[ 0 ] = ab;
			pc->sbytes[ 1 ] = bb;
			pc->sbytes[ 2 ] = cb;
		}

		return ab +bb +cb +3;
	}

	return 0;
}


/*--------------------------------------
 * missing any of the 2-input params?
 */
static unsigned int sat_missing_prm2(const struct SatState *ps,
                                   const char *a,   size_t abytes,
                                   const char *b,   size_t bbytes)
{
	return (!ps || !a || !b || !abytes || !bbytes) ;
}
#endif


/*--------------------------------------
 * returns compact string representation of 'add' appended to 'ps'
 *         0  if can not allocate, or invalid input, incl. empty 'add/abytes'
 */
static uint64_t sat_str_append(struct SatStrings *ps,
                                      const char *add, size_t abytes)
{
	uint64_t rc = 0;

	if (ps && add && abytes) {
		if (!ps->strs || (ps->used +abytes +1 > ps->allocd)) {
			size_t nb = ps->used +abytes +1 +STC_STR_UNITS;
			void *n   = realloc(ps->strs, nb);

			if (!n)
				return rc;

			ps->strs   = n;
			ps->allocd = nb;

			memset(&(ps->strs[ ps->used ]), 0, (nb - ps->used));
		}

		rc = offset2cstring(ps->used) + bytes2cstring(abytes);
// TODO: single-pass offset+byte to cstring macro

		memmove(&(ps->strs[ ps->used ]), add, abytes);
		ps->strs[ ps->used +abytes ] = '\0';

		ps->used += abytes +1;
	}

	return rc;
}


//--------------------------------------
// essentially, a specialized strncat()
//
static inline size_t sat_fmt_append1(struct SatFormat *pf, char add)
{
	if (pf && add && (pf->sbytes +1 <= sizeof(pf->s))) {
		if (pf->sbytes) {            // [ pf->sbytes -1 ] is current \0
			pf->s[ pf->sbytes -1 ] = add;
			pf->s[ pf->sbytes    ] = '\0';
			pf->sbytes++;

		} else {
			pf->s[ 0 ] = add;
			pf->s[ 1 ] = '\0';
			pf->sbytes = 2;
		}

		return pf->sbytes;
	}

	return 0;
}


/*--------------------------------------
 * essentially, a loop of strncat(), extending string in 'pf'
 * returns 0  if anything failed
 */
static int sat_fmt_append(struct SatFormat *pf, const void *add, size_t abytes)
{
	if (add && !abytes)
		abytes = strlen(add);

	if (pf && (pf->sbytes <= sizeof(pf->s)) && add && abytes) {
		if (pf->sbytes +abytes +1 > sizeof(pf->s))
			return 0;

		memmove(&(pf->s[ pf->sbytes -!!(pf->sbytes) ]),
		        add, abytes);

		pf->sbytes += abytes +1 -!!(pf->sbytes);

		pf->s[ pf->sbytes -1 ] = '\0';

		return pf->sbytes;
	}

	return 0;
}


/*--------------------------------------
 */
static int sat_fmt_append_u64(struct SatFormat *pf, uint64_t v)
{
	if (pf) {
		char fmt[ 19 +1 ] = { 0, };     // fits any u64 -> <= 19 digits
		size_t fb;

		fb = snprintf(fmt, sizeof(fmt), "%" PRIu64, v);

		return sat_fmt_append(pf, fmt, fb);
	}

	return 0;
}


/*--------------------------------------
 * is this a valid, 'non-empty' SAT state, with non-empty, and
 * valid-looking allocated/used limits?
 *
 * note: reports NULL strings as (not yet) valid
 */
static inline int has_valid_strings(const struct SatState *ps)
{
	return (ps && ps->s.strs && (ps->s.used <= ps->s.allocd));
}


/*--------------------------------------
 * is this a valid, 'non-empty' SAT state, with non-empty, and
 * valid-looking allocated/used limits?
 *
 * note: reports NULL strings as (not yet) valid
 */
static inline int has_valid_numbers(const struct SatState *ps)
{
	return (ps && ps->ns.n && (ps->ns.used <= ps->ns.allocd));
}


/*--------------------------------------
 * does the nr. of clauses appear sane?
 * empty 'ps' with no clauses yet also reported as invalid
 */
static inline int has_valid_clauses(const struct SatState *ps)
{
	if (!ps || !ps->c || !ps->c_used || !ps->c_allocd)
		return 0;

	return (ps->c_used <= ps->c_allocd);
}


/*--------------------------------------
 * no comments count as valid
 */
static inline int has_valid_comments(const struct SatState *ps)
{
	if (!ps)
		return 0;

	if (!ps->comments.strs)
		return 1;

	return (ps->comments.used <= ps->comments.allocd);
}


/*--------------------------------------
 * checks for place for string-terminating \0
 */
static inline int cstring_in_range(const struct SatState *ps, uint64_t s)
{
	return (ps && s &&
	        (cstring2offset(s) +cstring2bytes(s) +1 <= ps->s.used));
}


/*--------------------------------------
 * s expected to be valid, >0 compact string, within ps's string field
 */
static inline int is_valid_cstring1(const struct SatState *ps, uint64_t s)
{
	if (!has_valid_strings(ps))
		return 0;

	return cstring_in_range(ps, s);
}


/*--------------------------------------
 * s1/s2 are expected to be valid, >0 compact strings, within ps's string field
 */
static inline
int is_valid_cstring2(const struct SatState *ps, uint64_t s1, uint64_t s2)
{
	if (!has_valid_strings(ps))
		return 0;

	return cstring_in_range(ps, s1) && cstring_in_range(ps, s2);
}


/*--------------------------------------
 * note: Redis needs to update context; therefore, SatState not read-only
 */
static uint64_t sat_varname2int(struct SatState *ps,
                                     const char *name, size_t nbytes)
{
	if (!name || !nbytes || !ps || !ps->db.rd.ctx)
		return 0;

	return rds_lookup_main(ps->db.rd.ctx, name, nbytes);
}


/*--------------------------------------
 * register new name; assign new variable number
 * returns compact string ID upon success
 *         0  if anything failed
 *
 * mode selects which counter to increase:
 *      HSH_MAINHASH  primary/main variables
 *      HSH_ADDLHASH  indirect variables
 * TODO: need proper, not DB-bound IDs
 *
 * NOP if name is already known
 */
static uint64_t sat_name2cs(struct SatState *ps,
                                 const char *name, size_t nbytes,
                               unsigned int mode)
{
	uint64_t rc = 0;

	if (ps && name && nbytes) {
		uint64_t cs = 0;                      /* from database if >0 */

		do {
		if (ps->db.rd.ctx) {
			cs = sat_varname2int(ps, name, nbytes);
			if (cs && (cs != ~((uint64_t) 0))) {
				rc = cs;
				break;                         // found, report
			}
		}

		cs = sat_str_append(&( ps->s ), name, nbytes);
		if (!cs)
			break;

		if (ps->db.rd.ctx) {
			int dbrc = rds_str2db_main(ps->db.rd.ctx, name, nbytes,
			               (uint64_t) ps->addvars + ps->vars +1);
			if (dbrc < 0)
				break;
		}

		if (mode == HSH_MAINHASH) {
			ps->vars++;

		} else if (mode == HSH_ADDLHASH) {
			ps->addvars++;
		} else {
// ...report: unsupported mode...
		}

		rc = cs;
		} while (0);
	}

	return rc;
}


/*--------------------------------------
 * generate new (indirect) variable name; register into 'ps'; set *name fields
 * returns >0 if successful
 *
 * TODO: return compact string instead; simplifies typical calls
 */
static unsigned int sat_new_var(struct SatName *name,
                               struct SatState *ps)
{
	if (!name || !ps)
		return 0;

	*name = (struct SatName) SAT_NAME_INIT0;

	name->sbytes = snprintf((char *) name->s, sizeof(name->s),
	                        STC_NEWNAME_PREFIX "%u", ps->addvars +1);

	if (name->sbytes > sizeof(name->s))
		return 0;                              // SNH: number too wide

	name->cs = sat_name2cs(ps, (const char *) name->s, name->sbytes,
	                       HSH_ADDLHASH);

	return name->cs ? ps->addvars : 0;
}


/*---------------------------------
 * returns updated value
 */
static unsigned int sat_update_maxidx(struct SatState *ps)
{
	if (ps) {
		ps->maxvaridx = max_uint(ps->vars +ps->addvars, ps->maxvaridx);

// TODO: sanity check
	}

	return 0;
}


/*---------------------------------
 * assign new variable numbers [all consecutive]; expect n>0
 *
 * returns >0  upon success: index of first just-added variable
 *          0  if anything failed
 *
 * TODO: centralized overrun checking
 */
static uint64_t sat_next_vars(struct SatState *ps, unsigned int n)
{
	if (ps && n && (ps->addvars +n > ps->addvars)) {
		ps->addvars += n;

		sat_update_maxidx(ps);

		return ps->maxvaridx;
	}

	return 0;
}


/*---------------------------------
 * assign new variable number
 * returns 0  if anything failed
 */
static uint64_t sat_next_var(struct SatState *ps)
{
	return sat_next_vars(ps, 1);
}


/*--------------------------------------
 * TODO: is there a state machine (precedence rules) around these fields?
 */
static unsigned int sat_next_var_index(const struct SatState *ps)
{
	return ps ? (ps->vars + ps->addvars + 1) : 0;
}


//---------------------------------
static unsigned int sat_add_result(struct SatAdded *pa, uint32_t response) ;

static inline
struct SatState *sat_state_add(struct SatState *ps,
                                  unsigned int vars,
                                  unsigned int addl,
                                  unsigned int clauses) ;


/*---------------------------------
 * assign new variable number for result, unless it has been predefined
 * appends/registers to 'pa' as a response if non-NULL
 *
 * returns >0  final index, upon success
 *          0  if anything failed
 */
static uint64_t sat_register_result(struct SatState *ps,
	                            struct SatAdded *pa,
                                           uint32_t ret)
{
	ret = ret ? ret : (ps ? sat_next_vars(ps, 1) : 0);

	if (pa && ps && ret) {
		if (!sat_add_result(pa, ret))
			ret = 0;
	}

	return ret;
}


/*---------------------------------
 * register newly added variables and clauses' count to 'ps'
 * ret. value provided only to allow call chaining
 */
static int sat_register_additions(struct SatState *ps,
                            const struct SatAdded *pa)
{
	if (ps && pa) {                              // TODO: valid_additions()
		sat_state_add(ps, 0, pa->addvars, pa->clauses);
		return 1;
	}

	return 0;
}


/*---------------------------------
 * register new variables' and clauses' count; also assigns
 * new variable index for return value (if not yet defined with ret>0)
 *
 * returns >0 if successful: final return index
 *         0  if anything failed
 */
static uint64_t sat_register_news(struct SatState *ps,
	                          struct SatAdded *pa,
                                         uint32_t ret)
{
	if (ps && pa) {
		ret = sat_register_result(ps, pa, ret);

		if (!sat_register_additions(ps, pa) || !ret)
			ret = 0;

		return ret;
	}

	return 0;
}


#if 1    /*-----  delimiter: SAT/CNF-construction primitives  --------------*/
/* register +incr clauses (all functional)
 */
static void sat_register_clauses(struct SatState *ps, unsigned int incr)
{
	if (ps && incr) {
		ps->c_used    += incr;
		ps->nzclauses += incr;
	}
}


/*--------------------------------------
 * are 'flags' restricted to 1-bits of 'what'?
 */
static inline unsigned int flags_only(unsigned int flags, unsigned int what)
{
	return ((flags & ~what) == 0);
}


//--------------------------------------
static unsigned int sat_comment(struct SatState *ps,
                                     const char *c, size_t cbytes) ;

static uint64_t sat_comment1(struct SatState *ps,
                                  const char *c, size_t cbytes) ;

static unsigned int sat_const(struct SatState *ps,
                                     uint64_t a,
                                 unsigned int val) ;

// 'invert' turns OR into NOR
static unsigned int sat_or(struct SatName *name,
                          struct SatState *ps,
                                 uint64_t r,
                           const uint64_t *a, unsigned int an,
                             unsigned int flags) ;


/*----------------------------------------------------------------------------
 * appends clauses for R := XOR(A, B)
 *
 * truth table:
 *    A  B -R
 *   -A  B  R
 *    A -B  R
 *   -A -B -R
 *
 * 'r' supplies name for R; it is constructed otherwise into 'name'
 * when supplied, we do not need to register its name; newly constructed
 * 'name' is registered to 'ps'
 *
 * non-0 'invert' switches to NXOR (equality) from XOR
 *
 * NULL 'res' requires non-NULL 'name', which will be updated with
 * name of result variable
 */
static unsigned int sat_xor1(struct SatName *name,
                            struct SatState *ps,
                                   uint64_t r,
                                   uint64_t a,
                                   uint64_t b,
                                        int invert)
{
	struct SatClause *pc;
	unsigned int idx;

	if (!ps || !a || !b || (!name && !r))
		return 0;
	if (r && ((r == a) || (r == b)))
		return 0;                          // R=A or R=B makes no sense

	if (!is_valid_cstring2(ps, a, b))
		return 0;
	if (r && !is_valid_cstring1(ps, r))
		return 0;

// TODO: minimize A==B -> invalid condition, fixed False

// TODO: factor out: recurring init-or-pick-up condition
	if (!r) {
		if (!sat_new_var(name, ps))
			return 0;
		r = name->cs;
	}

	pc = sat_add_clauses(ps, &idx, 4);
	if (!pc)
		return 0;

	pc[ idx ].comment = sat_str_append(&( ps->comments ),
	                                   invert ? "EQ/NXOR" : "XOR",
	                                   invert ? 7         : 3);
	if (!pc[ idx ].comment)
		return 0;

	pc[ idx ].used = 3;
		//
	pc[ idx ].soffset[ 0 ] = cstring2offset(a);
	pc[ idx ].soffset[ 1 ] = cstring2offset(b);
	pc[ idx ].soffset[ 2 ] = cstring2offset(r);
		//
	pc[ idx ].sbytes [ 0 ] = cstring2bytes(a);
	pc[ idx ].sbytes [ 1 ] = cstring2bytes(b);
	pc[ idx ].sbytes [ 2 ] = cstring2bytes(r);
						// replicate common A/B/R
	sat_clone_strings(&(pc[ idx +1 ]), &(pc[ idx ]));
	sat_clone_strings(&(pc[ idx +2 ]), &(pc[ idx ]));
	sat_clone_strings(&(pc[ idx +3 ]), &(pc[ idx ]));

				// non-invert case:
				//     x80         x20
				//       v         v
				//        A    B   -R
				//       -A    B    R
				//        A   -B    R
				//       -A   -B   -R
				//            ^
				//            x40
				// invert (== instead of XOR) flips negated/R
	invert = invert ? 0x20 : 0;

	pc[ idx    ].neg[ 0 ] = (UINT64_C(0x20) ^ invert) << 56;
	pc[ idx +1 ].neg[ 0 ] = (UINT64_C(0x80) ^ invert) << 56;
	pc[ idx +2 ].neg[ 0 ] = (UINT64_C(0x40) ^ invert) << 56;
	pc[ idx +3 ].neg[ 0 ] = (UINT64_C(0xe0) ^ invert) << 56;

	return 4;
}


/*-----  range comparison primitives  --------------------------------------*/
// we split constants into 'runs' of identical bits
//
#define SAT_MAX_CMP_RUNS  ((unsigned int) 8)

// 1111-0-11 will result in [ 4, 1, 2, 0, ... ]
//
struct SatRuns {
	unsigned int bits[ SAT_MAX_CMP_RUNS ];
	unsigned int used;      // nr of entries in bits[]
	unsigned int total;     // sum(bits)
				// [0] always corresponds to run-of-1's
} ;
//
#define SAT_RUNS_INIT0  { {0,}, 0, 0, }


/*--------------------------------------
 * returns nr. of runs in 'n'
 *         0  if anything invalid, or if input is 0, which caller SHOULD
 *            have detected
 *        ~0  if something is out of range, such as too many runs
 *
 * TODO: can be compacted to a much simpler loop with
 * using nr-of-leading-zeroes intrinsic, if available (always with gcc/clang)
 *
 * APPLICATION NOTE:
 * due to our use of runs, we ignore LS run of 0's (they may not
 * decide comparisons, so are ignored for those purposes)
 */
static unsigned int sat_val2runs(struct SatRuns *pr, unsigned int n)
{
	unsigned int run = 0, mask;

	if (!pr || !n)
		return 0;

	*pr = (struct SatRuns) SAT_RUNS_INIT0;
	n   = (n ^ (n >> 1)) | !!((n & 3) == 2);
					//
					// leave only bits which start runs
					// incl. LS one if bit above is 1

	mask = ~((unsigned int) 0) - (~((unsigned int) 0) >> 1);

	pr->total = 8 * sizeof(unsigned int);

	while (!(mask & n)) {
		pr->total--;
		mask >>= 1;
	}

					// (mask & n) when entering loop
					// we just start the next run
	while (mask) {
		mask >>= 1;

		++run;
		if (run > ARRAY_ELEMS(pr->bits))
			return ~((unsigned int) 0);
		pr->used = run;

		pr->bits[ run-1 ] = 1;

		while (mask && !(mask & n)) {
			pr->bits[ run-1 ]++;
			mask >>= 1;
		}
	}

	return pr->total;
}


/*----------------------------------------------------------------------------
 * range comparisons: binary combination < N ('less than')
 *
 * 'r' supplies name for R; it is constructed otherwise into 'name'
 * when supplied, we do not need to register its name; newly constructed
 * 'name' is registered to 'ps'
 */
static unsigned int sat_lt(struct SatName *name,
                          struct SatState *ps,
                                 uint64_t r,
                           const uint64_t *a, unsigned int an,
                             unsigned int n)
{
	unsigned int idx, nruns, adds = 0, curr;
		// adds: total nr. of entries we add; curr: current building blk
	struct SatRuns runs = SAT_RUNS_INIT0;
	char cfmt[ STC_STR_MAX_BYTES +1 ];
	struct SatClause *pc;
	size_t cb;

	if (!ps || !a || !an)
		return 0;

	if (!n)
		return 0;                          // TODO: condition: never <0

	nruns = sat_val2runs(&runs, n);
	if (!nruns || (nruns == ~((unsigned int) 0)))
		return 0;                          // TODO: report out-of-range

	if (!r) {
		if (!sat_new_var(name, ps))
			return 0;
		r = name->cs;
	}

	cb  = snprintf(cfmt, sizeof(cfmt), "N[%ub]<CONST(%u)", an, n);
	idx = sat_state2clausecnt(ps);

	curr = sat_comment(ps, cfmt, cb);
	if (!curr)
		return 0;
	adds += curr;

					// const >= 2^runs.total
					// shorter field is trivially below
	if (an < runs.total) {
		curr = sat_comment(ps, "CONSTANT-TRUE", 13);
		return curr ? (adds + curr) : 0;
	}


					// OR(all bits above leading 1's run)
					// MUST be all-0, otherwise comparison
					// would trivially fail
	if (an > runs.total) {
		struct SatName discard = SAT_NAME_INIT0;
// only need clauses, but not implied variable

		sat_or(&discard, ps, 0, a, an - runs.total,
		       SAT_FL_INVERT /* NOR */);
	}
// RRR
(void) idx;
(void) pc;


//	pc  = sat_add_clauses(ps, &idx, an+1);
//	if (!pc)
//		return 0;

	return 0;
}


/*--------------------------------------
 * are the two 'an'-bit values equal? (or not equal, with 'invert')
 */
static unsigned int sat_eq(struct SatName *name,
                          struct SatState *ps,
                                 uint64_t r,
                           const uint64_t *a, unsigned int an,
                           const uint64_t *b,
                             unsigned int flags)
{
	uint64_t xors[ STC_CLS_MAX_ELEMS ] = { 0, };
	char descr[ STC_STR_MAX_BYTES +1 ];
	struct SatName eq = SAT_NAME_INIT0;
	unsigned int idx0, i;
	size_t cb;

	if (!ps || !a || !an || (an > STC_CLS_MAX_ELEMS) || !b)
		return 0;

	if (!flags_only(flags, (SAT_FL_INVERT | SAT_FL_ADD_VAR)))
		return 0;

	idx0 = sat_state2clausecnt(ps);

	cb = snprintf(descr, sizeof(descr), "%s" "EQ(%u)",
	              (SAT_FL_INVERT & flags) ? "NOT-" : "", an);
		/**/
	if (!sat_comment(ps, descr, cb))
		return 0;

	for (i=0; i<an; ++i) {
		if (!sat_xor1(&eq, ps, 0, a[i], b[i], 0))
			return 0;
		xors[i] = eq.cs;
	}

			// == means none of the XORs is True         -> NOR
			// != means at least one of the XORs is true -> OR

	if (!sat_or(name, ps, r, xors, an,
	            SAT_FL_INVERT ^ (SAT_FL_INVERT & flags)))
		return 0;

	return sat_state2clausecnt(ps) - idx0;
}


/*--------------------------------------
 * are the two numbers equal, or either is all-0?
 *
 * turns into  NOR(a[]) | NOR(b[]) | NOT-EQ(a[], b[])   ->
 *                          OR(XOR(bits/1) ... XOR(bits/N))
 *      (1) NOR of any all-0 satisfies or
 *      (2) at least one of the XOR's is True -> a[] != b[]
 */
static unsigned int sat_neq_or0(struct SatName *name,
                               struct SatState *ps,
                                      uint64_t r,
                                const uint64_t *a, unsigned int an,
                                const uint64_t *b)
{
	struct SatName nor1 = SAT_NAME_INIT0,
	               nor2 = SAT_NAME_INIT0,
	                 eq = SAT_NAME_INIT0;
	char descr[ STC_STR_MAX_BYTES +1 ];
	unsigned int idx, idx0;
	struct SatClause *pc;
	size_t cb;

	if (!ps || !a || !an || (an > STC_CLS_MAX_ELEMS) || !b)
		return 0;

	if (!r) {
		if (!sat_new_var(name, ps))
			return 0;
		r = name->cs;
	}

	idx0 = ps->c_used;

	cb = snprintf(descr, sizeof(descr), "EQ-OR-ZERO(%u)", an);
		/**/
	if (!sat_comment(ps, descr, cb))
		return 0;

	if (!sat_or(&nor1, ps, 0, a, an, SAT_FL_INVERT /* NOR */) ||
	    !sat_or(&nor2, ps, 0, b, an, SAT_FL_INVERT /* NOR */) ||
	    !sat_eq(&eq,   ps, 0, a, an, b, SAT_FL_INVERT /* != */))
		return 0;

	// nor1, nor2, eq are NOR(a[]), NOR(b[]), (a[] <=> b[]), respectively

	pc = sat_add_clauses(ps, &idx, 1);
	if (!pc)
		return 0;

	                               // NOR(a[]) | NOR(b[]) | -NXOR(a[], b[])
	pc[ idx ].used = 3;
	pc[ idx ].neg[ 0 ] = ((uint64_t) 0x20) << 56;               // + + -

	pc[ idx ].soffset[ 0 ] = cstring2offset(nor1.cs);           // NOR(a[])
	pc[ idx ].sbytes [ 0 ] =  cstring2bytes(nor1.cs);

	pc[ idx ].soffset[ 1 ] = cstring2offset(nor2.cs);           // NOR(b[])
	pc[ idx ].sbytes [ 1 ] =  cstring2bytes(nor2.cs);

	pc[ idx ].soffset[ 2 ] = cstring2offset(eq.cs);             // -EQ(b[])
	pc[ idx ].sbytes [ 2 ] =  cstring2bytes(eq.cs);

	return idx - idx0;
}


/*--------------------------------------
 * common sanity check for array-input, N+1-clause functions (n-plus-1 -> np1)
 */
static unsigned int valid_sat_params(const struct SatState *ps)
{
	if (!ps)
		return 0;

	if (ps->s.strs && !has_valid_strings(ps))
		return 0;

	if (ps->ns.n   && !has_valid_numbers(ps))
		return 0;

	return 1;
}


/*--------------------------------------
 * common sanity check for array-input, N+1-clause functions (n-plus-1 -> np1)
 */
static unsigned int
valid_np1_params(const struct SatName *name,
                const struct SatState *ps,
                             uint64_t r,
                       const uint64_t *a, unsigned int an)
{
	unsigned int i;

	if (!valid_sat_params(ps))
		return 0;

	if (!a || (!name && !r))
		return 0;

	if (an+1 >= STC_CLS_MAX_ELEMS)
		return 0;         // N+1 terms, must fit per-clause limit

	for (i=0; i<an; ++i) {
		if (!is_valid_cstring1(ps, a[i]))
			return 0;
	}
	if (r && !is_valid_cstring1(ps, r))
		return 0;

	return 1;
}


/*--------------------------------------
 * appends clauses for R := OR(...variables of a[]...)
 * supply at least one variable; reports error otherwise
 *
 * clauses:
 *      A | B | ... | H | -R    -- R -> (A | B | ... | H)
 *     -A | R                   -- together: (A | B | ... | H) -> R
 *     -B | R
 *     ...
 *     -H | R
 *
 * 'flags' may contain SAT_FL_INVERT (-> NOR) or SAT_FL_ADD_VAR
 *
 * returns 0 if anything invalid (which, unfortunately, could be
 * valid with 1-bit input)
 */
static unsigned int sat_or(struct SatName *name,
                          struct SatState *ps,
                                 uint64_t r,
                           const uint64_t *a, unsigned int an,
                             unsigned int flags)
{
	char descr[ STC_STR_MAX_BYTES +1 ];
	struct SatClause *pc;
	unsigned int idx, i;
	size_t cb;

	if (!valid_np1_params(name, ps, r, a, an))
		return 0;

	if (!flags_only(flags, (SAT_FL_INVERT | SAT_FL_ADD_VAR)))
		return 0;

	if (!r) {
		if (!sat_new_var(name, ps))
			return 0;
		r = name->cs;
	}

				// trivial cases:  OR(A) -> A
				//                NOR(A) -> -A
				// neither case requires a new variable
				//
				// TODO: check for generic new-variable
				// propagation, incl. reporting an inverted one
				//
				// keep '||' to ensure comment and constant
				// added in expected order---even if it
				// is irrelevant for CNF-only form, which
				// skips comments
	if (an == 1) {
		if (name)
			name->cs = a[0];        // OR(A) -> A  or  NOR(A) -> -A

		if (SAT_FL_INVERT & flags) {
			if (name)
				name->invert = 1;

			if (!sat_comment(ps, "NOR(v)->NOT(v)", 14) ||
			    !sat_const(ps, a[0], 0))
				return 0;

		} else if (name) {
			if (!sat_comment(ps, "OR(v)->v", 8) ||
			    !sat_const(ps, a[0], 1))
				return 0;
		}
		return 2;
	}

	if (!an)
		return 0;          // explicit check for >=1 input/s

	pc = sat_add_clauses(ps, &idx, an+1);
	if (!pc)
		return 0;

	cb = snprintf(descr, sizeof(descr), "%s" "OR(%u)",
	              (SAT_FL_INVERT & flags) ? "N" : "", an);
		/**/
	pc[ idx ].comment = sat_str_append(&( ps->comments ), descr, cb);
	if (!pc[ idx ].comment)
		return 0;


	pc[ idx ].used = an+1;
				// a[0] | a[1] | ... | a[an-1] | <NOT(R) or R>
	for (i=0; i<an; ++i) {
		pc[ idx ].soffset[ i ] = cstring2offset(a[ i ]);
		pc[ idx ].sbytes [ i ] =  cstring2bytes(a[ i ]);
	}
	pc[ idx ].soffset[ an ] = cstring2offset(r);
	pc[ idx ].sbytes [ an ] =  cstring2bytes(r);
		//
	pc[ idx ].neg[ 0 ] = ((uint64_t) !(SAT_FL_INVERT & flags)) << (63 - an);
						// NOT(R) (=OR) or R (=NOR)


	for (i=0; i<an; ++i) {
		pc[ idx +1 +i ].soffset[ 0 ] = cstring2offset(a[ i ]);
		pc[ idx +1 +i ].sbytes [ 0 ] =  cstring2bytes(a[ i ]);
		pc[ idx +1 +i ].soffset[ 1 ] = cstring2offset(r);
		pc[ idx +1 +i ].sbytes [ 1 ] =  cstring2bytes(r);
						// NOT(A) | R ... NOT(H) | R

		pc[ idx +1 +i ].neg[ 0 ] =
			((uint64_t) !!(SAT_FL_INVERT & flags)) << 62;
						// R (=OR) or NOT(R) (=NOR)

		pc[ idx +1 +i ].used     = 2;
	}

	return 1+an;
}


/*--------------------------------------
 * appends clauses for R := NAND(...variables of a[]...)
 *
 * clauses:
 *     -A | -B | ... | -H | -R  -- -R -> (-A | -B | ... | -H)
 *      A | R                   -- together: (A & B & ... & H) -> R   XXX
 *      B | R
 *      ...
 *      H | R
 */
static unsigned int sat_nand(struct SatName *name,
                            struct SatState *ps,
                                   uint64_t r,
                                   uint64_t *a, unsigned int an)
{
	struct SatClause *pc;
	unsigned int idx, i;

	if (!valid_np1_params(name, ps, r, a, an))
		return 0;

	if (!r) {
		if (!sat_new_var(name, ps))
			return 0;
		r = name->cs;
	}

	pc = sat_add_clauses(ps, &idx, an+1);
	if (!pc)
		return 0;

	pc[ idx ].comment = sat_str_append(&( ps->comments ), "NAND", 4);
	if (!pc[ idx ].comment)
		return 0;

	pc[ idx ].used = an+1;
			// NOT(a[0]) | NOT(a[1]) | ... | NOT(a[an-1]) | NOT(R)
	for (i=0; i<an; ++i) {
		pc[ idx ].soffset[ i ] = cstring2offset(a[ i ]);
		pc[ idx ].sbytes [ i ] =  cstring2bytes(a[ i ]);
	}
	pc[ idx ].soffset[ an ] = cstring2offset(r);
	pc[ idx ].sbytes [ an ] =  cstring2bytes(r);
		//
	pc[ idx ].neg[ 0 ] = ~((uint64_t) 0) - ((~((uint64_t) 0)) >> (an+1));
					// NOT(...all used variables...)


	for (i=0; i<an; ++i) {
		pc[ idx +1 +i ].soffset[ 0 ] = cstring2offset(a[ i ]);
		pc[ idx +1 +i ].sbytes [ 0 ] =  cstring2bytes(a[ i ]);
		pc[ idx +1 +i ].soffset[ 1 ] = cstring2offset(r);
		pc[ idx +1 +i ].sbytes [ 1 ] =  cstring2bytes(r);
							// A | R ... H | R
		pc[ idx +1 +i ].neg[0] = 0;        // was already 0-initialized
		pc[ idx +1 +i ].used   = 2;
	}

	return 1+an;
}


/*----------------------------------------------------------------------------
 * 1-of-N construction
 *
 * the general idea is to create a hierarchy of 'commander variables'
 * where (1) the top one is 1 (or possibly 0, with 0-of-N allowed)
 * (2) not more than one of the lowest-level commander variables
 * is 1 (3)
 *
 * see
 * Kliebert, Kwon: Efficient CNF encoding for selecting 1 of N objects,
 * www.cs.cmu.edu/~wklieber/papers/
 *     2007_efficient-cnf-encoding-for-selecting-1.pdf
 * [accessed 2023-02-24]
 *
 * with N=2 fanout, listing commanders is quite straightforward with
 * two aux. arrays.  each term resembles an XOR, with a clause which
 * prohibits both inputs True:
 *      A  B -R
 *      A -B  R
 *     -A  B  R
 *     -A -B
 *
 * the top-level commander variable then reports whether
 * at least one of the subordinate variables has been True.
 */

// SIZE NOTE: u64[] this much is allocated on the stack
#define  SAT_MAX_CMD_VARS  ((unsigned int) 128)     /* per level */
//
// TODO: work out proper limits

struct Sat1Ncmd {
	uint64_t v[ SAT_MAX_CMD_VARS ];

	unsigned int used;
} ;
//
#define SAT_1NCMD_INIT0  { { 0, }, 0, }


/*--------------------------------------
 * register A,B -> R for one 1-of-N commander variable pair
 */
static unsigned int sat_1ofn_1pair(struct SatState *ps,
                                          uint64_t a,
                                          uint64_t b,
                                          uint64_t r)
{
	struct SatClause *pc;
	unsigned int idx;

	pc = sat_add_clauses(ps, &idx, 4);
	if (!pc)
		return 0;

					// truth table:
					//      A  B -R
					//      A -B  R
					//     -A  B  R
					//     -A -B

// TODO: recurring theme; add a wrapper fn

	pc[ idx ].used = 3;     // A/B/R terms
		//
	pc[ idx ].soffset[ 0 ] = cstring2offset(a);
	pc[ idx ].soffset[ 1 ] = cstring2offset(b);
	pc[ idx ].soffset[ 2 ] = cstring2offset(r);
	pc[ idx ].sbytes [ 0 ] = cstring2bytes(a);
	pc[ idx ].sbytes [ 1 ] = cstring2bytes(b);
	pc[ idx ].sbytes [ 2 ] = cstring2bytes(r);
						// replicate common A/B/R
	sat_clone_strings(&(pc[ idx +1 ]), &(pc[ idx ]));
	sat_clone_strings(&(pc[ idx +2 ]), &(pc[ idx ]));

	pc[ idx    ].neg[ 0 ] = UINT64_C(0x20) << 56;    //  A  B -R
	pc[ idx +1 ].neg[ 0 ] = UINT64_C(0x40) << 56;    //  A -B  R
	pc[ idx +2 ].neg[ 0 ] = UINT64_C(0x80) << 56;    // -A  B  R


	pc[ idx +3 ].used = 2;     // A/B term
		//
	pc[ idx +3 ].soffset[ 0 ] = cstring2offset(a);
	pc[ idx +3 ].soffset[ 1 ] = cstring2offset(b);
	pc[ idx +3 ].sbytes [ 0 ] = cstring2bytes(a);
	pc[ idx +3 ].sbytes [ 1 ] = cstring2bytes(b);

	pc[ idx +2 ].neg[ 0 ] = UINT64_C(0xc0) << 56;    // -A -B

	return ps->c_used;
}


/*--------------------------------------
 * construct hierarchy of comparison expressions for 1-of-N tree
 * with fanout of 2: each level halves the nr. of variables
 *
 * final result is 'end', which MUST have already been registered by caller
 */
static unsigned int sat_1ofn_core2x(struct SatState *ps,
                                           uint64_t end,
                                     const uint64_t *a, unsigned int an)
{
	struct SatName name = SAT_NAME_INIT0;
	struct Sat1Ncmd h = SAT_1NCMD_INIT0;

	if (!ps || !a || !an || (an > STC_CLS_MAX_ELEMS))
		return 0;

				// input is (a, an) during first iteration
				// h.v[] during subsequent iterations

				// final 1/2 entries propagate directy to 'end'
	while (an > 1) {
		unsigned int i, wr = 0;

		for (i=0; i < an /2; ++i) {                   // A,B -> R pairs
			if (an == 2) {
				name.cs = end;
			} else {
				if (!sat_new_var(&name, ps))
					return 0;
			}

			if (!sat_1ofn_1pair(ps, a[i+i], a[i+i+1], name.cs))
				return 0;

			h.v[ wr ] = name.cs;
			++wr;
		}

		if (an & 1) {               // odd count: propagate directly up
			h.v[ wr ] = a[ an-1 ];
			++wr;
		}

		if ((const uint64_t *) a != (const uint64_t *) h.v)
			a = h.v;
		an = wr;
	}

(void) end;

	return 1;
}


/*--------------------------------------
 * 1-of-N; optionally 0/1-of-N is True of a[]
 *
 * 'allow0' enables 0/1-of-N comparison
 */
static unsigned int sat_1ofn(struct SatName *name,
                            struct SatState *ps,
                                   uint64_t r,
                                   uint64_t *a, unsigned int an,
                                        int allow0)
{
	char descr[ STC_STR_MAX_BYTES +1 ];
	unsigned int nzused;
	size_t db;

	if (!valid_np1_params(name, ps, r, a, an))
		return 0;
	                                               // trivial special cases
	if (an == 1)
		return 0;            // var stands for itself, needs no clauses

	nzused = ps->nzclauses;

	db = snprintf(descr, sizeof(descr), "%s1-of-N(%u)",
	                                    allow0 ? "0/" : "", an);
	if (!sat_comment(ps, descr, db))
		return 0;

	if (an == 2) {
		return allow0 ? sat_nand(name, ps, r, a, an)
		              : sat_xor1(name, ps, r, a[0], a[1], 0);
	}

	if (!r) {
		if (!sat_new_var(name, ps))
			return 0;
		r = name->cs;
	}

	if (!sat_1ofn_core2x(ps, r, a, an))
		return 0;

	if (allow0) {       // nothing to do: top-level var is irrelevant
	                    // construct only ensures no subordinate
	                    // commander variable (-> var pair) generates
	                    // conflict with both one
// ...
	} else {
		if (!sat_const(ps, r, 1))              // top-level cmd is True
			return 0;
	}

	return (ps->nzclauses -nzused);
}


/*--------------------------------------
 * 1-of-N, special cases in the beginning
 * returns >0  if accepted (1+nr of real clauses appended to 'ps')
 *         ~0  if input is inconsistent
 *          0  if not recognized as special case; caller must process
 */
static unsigned int sat_1ofn_few(struct SatName *name,
                                struct SatState *ps,
                                       uint64_t r,
                                       uint64_t *a, unsigned int an,
                                            int allow0)
{
	unsigned int rc = 0;

	if (!valid_np1_params(name, ps, r, a, an))
		return ~((unsigned int) 0);

	if (an == 1) {
		if (allow0) {            // var is 0/1
			return 1;        // stands for itself, needs no clauses

		} else {                 // var is 1
			if (!sat_comment(ps, "1-of-N(v)->v", 12) ||
			    !sat_const(ps, a[0], 1))
				return ~((unsigned int) 0);
			return 2;
		}
	}

	if (an == 2) {
		rc = allow0 ? sat_nand(name, ps, r, a, an)
		            : sat_xor1(name, ps, r, a[0], a[1], 0);
		return rc ? rc+1 : ~((unsigned int) 0);
	}

// RRR
	if (an == 3) {
	}

	return 0;
}


/*--------------------------------------
 * find P+Q for reasonable P*Q decoding of 'n' entries
 *
 * TODO: table-driven, or pick optimal P+Q based on cost estimates
 * which, as a side effect, remove math.h dependency on sqrt
 */
static unsigned int sat_1ofn_prod_pq(unsigned int *q, unsigned int n)
{
	unsigned int p, resq;

	if (q)
		*q = 0;

	p = (unsigned int) sqrt(n);

	if (p * p == n) {
		resq = p;

	} else if (p * (p+1) >= n) {
		resq = p+1;

	} else if ((p + 1) * (p + 1) >= n) {
		++p;
		resq = p;

	} else if ((p + 1) * (p + 2) >= n) {
		++p;
		resq = p+1;
	} else {
		p = 0;                // sort-of-assert
	}

	if (q)
		*q = resq;

	return p;
}


/*--------------------------------------
 * 'force' adds explicit clause ensuring 'result' is True
 *
 * 'two-product encoding of 0/1-of-N'
 *   1) construct P*Q matrix with P*Q >= N
 *   2) variables 1..N <-> entries in matrix
 *   3) 1-of-N: ensure 1-of-P (X) and 1-of-Q (Y)
 *     3.1) selected entry is intersection
 *   4) 0-of-N: allow NOR(P) AND NOR(Q) (==NOT(P OR Q)) as well
 *   5) only N product variables are used if N<P*Q
 *
 * note: hierarchical decomposition of 1-of-P/Q
 * TODO: use template for small P/Q which we expect to encounter
 *
 * see:
 * Chen: A new SAT encoding of the at-most-one constraint
 * 2010-07
 * TODO: URL
 */
static unsigned int sat_1ofn_prod(struct SatName *name,
                                 struct SatState *ps,
                                        uint64_t r,
                                        uint64_t *a, unsigned int an,
                                             int allow0)
{
	unsigned int rc = 0, p = 0, q = 0;

	if (!valid_np1_params(name, ps, r, a, an))
		return 0;

	rc = sat_1ofn_few(name, ps, r, a, an, allow0);

	do {
	if (rc == ~((unsigned int) 0)) {
		rc = 0;                                     // something failed
	} else if (rc) {
		--rc;                  // success: 1-based to 0-based reporting
		break;
	}

	p = sat_1ofn_prod_pq(&q, an);
	if (!p || !q)
		break;                 // rc=0, from above

// N <= P * Q
// RRR
#if 0
			## 'frame' variables, rows (Q) and columns (P)
			##
	pvars = [sat_new_varname2(sat, prefix=f'XY{ len(vars) }C')
	                              for i in range(p)]
			##
	qvars = [sat_new_varname2(sat, prefix=f'XY{ len(vars) }R')
	                              for i in range(q)]
#endif

	} while (0);

	return rc;
}


#if 0   // 1-of-N, product-based decoder   ----------------------------------
##-----------------------------------------
## hardwired 0/1-of-N for small N with trivial expressions
##
## returns None if not handled
##         [ top-level variable, [ newly added variables, ], clauses, comment ]
##             if solution is applicable
##
def satsolv_1n_few(sat, vars, nr=0, allow0=False, result=None, force=False):
	if len(vars) == 1:
		if allow0:                                ## A=0/1 -> no clause
			return [ [], [], [], '', ]
		else:
				## explicit clause forcing var to True
				## do not bother trimming replicated clauses
				##
			cls = [ vars[0] ]  if force  else []

			return [ vars[0], [], cls, '', ]      ## 1-of-N(A) == A


	##------------------------------
	if len(vars) == 2:                          ## 1-of-A/B  or  0/1-of-A/B
		if allow0:                     ## reject simultaneous True only
			if result == None:
				result = sat_new_varname2(sat, 'NAND')

			cls = [ f'-{ vars[0] } -{ vars[1] }', ]
			cmt = f'at-most-1({result})=>NAND({vars[0]},{vars[1]})'
			return [ [], [], cls, cmt, ]
						## only clause, no new variable
## TODO: merge return paths
		if result == None:
			result = sat_new_varname2(sat, 'N1xXOR')

		cls, _, _ = satsolv_xor1(vars[0], vars[1], result=result)
		cmt = f'at-most-1({result}) => ({vars[0]} XOR {vars[1]})'

		if force:
			cls.append(satsolv_const(result))        ## XOR is true

		return [ result, [ result, ], cls, cmt, ]


	##------------------------------
	if len(vars) == 3:
## TODO: use a more compact encoding than OR+not-pairs
				## no pair of variables is simultaneously true
		cls = [ f'-{v1} -{v2}'  for v1, v2  in allpairs(vars) ]
		or3 = []
## TODO: proper signs and indexing

		if not allow0:
			result = sat_new_varname2(sat,'THREE2ONEx')
			cls0, or3, _ = satsolv_or('', vars, result)

			cls.extend(cls0)
##			cls.append(satsolv_const(result))
##							## at least one is true

			or3 = [ or3, ]

		return [ result, or3, cls, '', ]


	return None


##-----------------------------------------
## 1-of-N or 0-of-N (selected by 'allow0')
##
## returns [ control variable, [ new/intermediate variables],
##           [ new clauses ], comment ]  tuple
##
## 'force' adds explicit clause ensuring 'result' is True
##
## 'two-product encoding of 0/1-of-N'
##   1) construct P*Q matrix with P*Q >= N
##   2) variables 1..N <-> entries in matrix
##   3) 1-of-N: ensure 1-of-P (X) and 1-of-Q (Y)
##     3.1) selected entry is intersection
##   4) 0-of-N: allow NOR(P) AND NOR(Q) (==NOT(P OR Q)) as well
##   5) only N product variables are used if N<P*Q
##
## note: hierarchical decomposition of 1-of-P/Q
## TODO: use template for small P/Q which we expect to encounter
##
## see:
## Chen: A new SAT encoding of the at-most-one constraint
## 2010-07
## TODO: URL
##
def satsolv_1ofn_2prod(sat, vars, result=None, force=False, allow0=False):
## sat next vars -> nr
	nr, comm, expr = 0, '', []

## TODO: trim added-vs-original variables properly

				## before-after: new/intermediate variables
	nvars_orig = satsolv_nr_of_added_vars(sat)

	expr = f'1-OF-[{ len(vars) }]({ ",".join(vars) })'

	r = satsolv_1n_few(sat, vars, nr=nr, allow0=allow0, result=result)
	if r:
		return r[0], r[1], r[2], r[3]

			## assume ~square P*Q is optimal
			## TODO: minimize (cost(P) + cost(Q)) -> select P, Q
			##
	p = int(math.sqrt(len(vars)))
	if (p ** 2 == len(vars)):
		q = p
	elif (p * (p+1) >= len(vars)):
		q = p + 1
	elif ((p + 1) ** 2 >= len(vars)):
		p, q = p + 1, p + 1
	elif ((p + 1) * (p + 2) >= len(vars)):
		p, q = p + 1, p + 2
	else:
		assert(0)  ## ...optimal selection would eliminate selection...

	if result == None:
		result = sat_new_varname2(sat,
		                 prefix='N01:' if allow0 else 'N1x')

	comm = f'{ 0  if allow0  else 1 }-of-{ len(vars) } <-> {p}*{q}'
	cls, nvars = [], []

			## 'frame' variables, rows (Q) and columns (P)
			##
	pvars = [sat_new_varname2(sat, prefix=f'XY{ len(vars) }C')
	                              for i in range(p)]
			##
	qvars = [sat_new_varname2(sat, prefix=f'XY{ len(vars) }R')
	                              for i in range(q)]

					## group inputs as p-times-q product
					##
	xyvars = [vars[ i*p : (i+1)*p ]  for i in range(q)]
					##
					## last row may contain less
					## variables (if N < P*Q)

	if True:
		printf(f'## P=1-of-{p} x Q=1-of-{q}')
		printf(f'## VARS(P)[{ len(pvars) }]={ pvars }')
		printf(f'## VARS(Q)[{ len(qvars) }]={ qvars }')

	pv, pnvars, pcls, _ = satsolv_1ofn_2prod(sat, pvars, allow0=allow0)
	qv, qnvars, qcls, _ = satsolv_1ofn_2prod(sat, qvars, allow0=allow0)
	printf(f'## VAR.P={ pv } [{ len(pcls) }] ', pcls)
	printf(f'## VAR.Q={ qv } [{ len(qcls) }] ', qcls)

	cls.extend(pcls)
	cls.extend(qcls)
	nvars.extend(pnvars)
	nvars.extend(qnvars)

				## both MUST be true for 1-by-1 intersection
				##
	pq_clauses, _, _ = satsolv_and('', [ pv, qv, ], result=result)
	cls.extend(pq_clauses)

				## at-most-1(vars): each 'var' corresponds to
				## not more than one pvar/qvar ->
				##     (NOT(v) OR p) AND (NOT(v) OR q)
				##
	for ri, row in enumerate(xyvars):                  ## loop(q), row
		for ci, col in enumerate(row):             ## loop(p), column
			cls.append(f'-{ col } { pvars[ci] }')
			cls.append(f'-{ col } { qvars[ri] }')

	nvars_after = satsolv_nr_of_added_vars(sat)

	if force:
		cls.append(f'{ result }')   ## 0/1-of-N must hold at this level

	printf(f'## ADDED.VARS=+{ satsolv_nr_of_added_vars(sat) - nvars_orig }')
		##
	if nvars_after > nvars_orig:
		vlist = ", ".join(sat["vars"][ nvars_orig:nvars_after ])
		printf(f'## ADDED.VARS=[{ vlist }]')

	return result, [], cls, comm
#endif   // /product-based 1-of-N decoder


/*--------------------------------------
 * registers single-entry comment to last used entry of 'ps'
 *
 * returns >0  if comment has been registered and appended
 *         0   if anything failed
 */
static uint64_t sat_comment1(struct SatState *ps,
                                  const char *c, size_t cbytes)
{
	unsigned int idx = ps ? ps->c_used : ~((unsigned int) 0);

	if (!ps || !ps->c || !c || !cbytes || !idx ||
	    (idx > ps->c_used)                     ||
	    (ps->c_used > ps->c_allocd))
		return 0;

	ps->c[ idx -1 ].comment = sat_str_append(&( ps->comments ), c, cbytes);

	return ps->c[ idx -1 ].comment;
}


/*--------------------------------------
 * appends single-line comment as new entry
 */
static unsigned int sat_comment(struct SatState *ps,
                                     const char *c, size_t cbytes)
{
	if (!ps || !c || !cbytes)
		return 0;

	if (sat_ensure_clauses(ps, 1) <0)
		return 0;

	ps->c_used++;

	return sat_comment1(ps, c, cbytes) ? 1 : 0;
}


/*--------------------------------------
 * appends a direct Boolean constant--such as precalculated fns for SAT control
 * 'val' is restricted to 0/1; we may allow other combinations in the future
 */
static unsigned int sat_const(struct SatState *ps,
                                     uint64_t a,
                                 unsigned int val)
{
	struct SatClause *pc;
	unsigned int idx;

	if (sat_ensure_clauses(ps, 1) <0)
		return 0;

	if (val > 1)
		return 0;

	pc  = ps->c;
	idx = ps->c_used;

	sat_register_clauses(ps, 1);

	pc[ idx ].used = 1;
	pc[ idx ].soffset[ 0 ] = cstring2offset(a);
	pc[ idx ].sbytes [ 0 ] =  cstring2bytes(a);

	pc[ idx ].neg[ 0 ] = val ? 0 : (UINT64_C(1) << 63);

	return 1;
}


/*--------------------------------------
 * appends clauses for R := AND(...variables of a[]...)
 *
 * clauses:
 *     -A | -B | ... | -H | R    -- R -> (A & B & ... & H)
 *      A | -R                   -- together: (A & B & ... & H) -> R
 *      B | -R
 *     ...
 *      H | -R
 */
static unsigned int sat_and(struct SatName *name,
                           struct SatState *ps,
                                  uint64_t r,
                                  uint64_t *a, unsigned int an)
{
	struct SatClause *pc;
	unsigned int idx, i;

	if (!valid_np1_params(name, ps, r, a, an))
		return 0;

	if (sat_ensure_clauses(ps, an+1) <0)
		return 0;

	if (!r) {
		if (!sat_new_var(name, ps))
			return 0;
		r = name->cs;
	}

	pc  = ps->c;
	idx = ps->c_used;

	sat_register_clauses(ps, an +1);

	pc[ idx ].comment = sat_str_append(&( ps->comments ), "AND", 3);
	if (!pc[ idx ].comment)
		return 0;


	pc[ idx ].used = an+1;
			// NOT(a[0]) | NOT(a[1]) | ... | NOT(a[an-1]) | R
	for (i=0; i<an; ++i) {
		pc[ idx ].soffset[ i ] = cstring2offset(a[ i ]);
		pc[ idx ].sbytes [ i ] =  cstring2bytes(a[ i ]);
	}
	pc[ idx ].soffset[ an ] = cstring2offset(r);
	pc[ idx ].sbytes [ an ] =  cstring2bytes(r);
		//
	pc[ idx ].neg[ 0 ] = ~((uint64_t) 0) - ((~((uint64_t) 0)) >> an);


	for (i=0; i<an; ++i) {
		pc[ idx +1 +i ].soffset[ 0 ] = cstring2offset(a[ i ]);
		pc[ idx +1 +i ].sbytes [ 0 ] =  cstring2bytes(a[ i ]);
		pc[ idx +1 +i ].soffset[ 1 ] = cstring2offset(r);
		pc[ idx +1 +i ].sbytes [ 1 ] =  cstring2bytes(r);
						// A | NOT(R) ... H | NOT(R)

		pc[ idx +1 +i ].neg[ 0 ] = UINT64_C(0x40) << 56;
		pc[ idx +1 +i ].used     = 2;
	}

	return 1+an;
}
#endif   /*-----  /delimiter: SAT/CNF-construction primitives  -------------*/


/*--------------------------------------
 * does this mode ask for expanded comments? (such as "V1 = OR(A, B)")
 * see SatReport_t for bits of mode
 */
static int include_explanations(uint32_t mode)
{
	if ((STC_R_NOCOMMENT | STC_R_NOFRAME | STC_R_VARLIST_ONLY |
	     STC_R_CLAUSE_ONLY) & mode)
	{
		return 0;               // these bits all prohibit explanations
	}

	return 1;
}


/*--------------------------------------
 * allow chaining as 'in comment' marker
 */
static unsigned int sat_start_comment(struct SatFormat *fmt)
{
	if (fmt)
		sat_fmt_append(fmt, "c ", 2);

	return 1;
}


/*----------------------------------------------------------------------------
 * 'mode' is bitmask, see SatReport_t for bits
 * see sat_format_int_clauses() for numeric-only form
 *
 * note: DB access may need to update context etc. in 'ps', so not constant
 */
static int sat_print_clauses(struct SatState *ps, uint32_t mode)
{
	const struct SatClause *pc = ps ? ps-> c : NULL;
	struct SatFormat fmt = SAT_FORMAT0;
	unsigned int c, v, nzclauses = 0;

// TODO: now we have valid_params valid_sat_params();
// factor out + point to that

	if (!has_valid_strings(ps) || !has_valid_clauses(ps) ||
	    !has_valid_comments(ps))
		return 0;

	if (!(STC_R_NOFRAME & mode)) {
		if (STC_R_EMBED & mode)
			printf("%s", STC_REP_PREFIX);

		printf("p cnf %u %u\n",
		       ps->vars +ps->addvars, ps->nzclauses);
	}

	for (c=0; c<ps->c_used; ++c) {
		uint64_t signs = pc[c].neg[0], mask = UINT64_C(1) << 63;
		int in_comment = 0;

		fmt = (struct SatFormat) SAT_FORMAT0;

// currently, hardwired single-u64 sign/mask; break here if ever growing:
			BUILD_ASSERT(ARRAY_ELEMS(pc->neg) == 1);

		if (!is_valid_clauseelem_count(pc[c].used))
			continue;

		if (pc[c].comment && include_explanations(mode)) {
			size_t offs  = cstring2offset(pc[c].comment),
			       bytes =  cstring2bytes(pc[c].comment);

			if (STC_R_EMBED & mode)
				printf("%s", STC_REP_PREFIX);

			sat_start_comment(&fmt);
// TODO: comment equivalent of is_valid_cstring1()
			sat_fmt_append(&fmt, &( ps->comments.strs[ offs ] ),
			               bytes);
			printf("%s\n", fmt.s);

			in_comment = 0;                             // new line
			fmt = (struct SatFormat) SAT_FORMAT0;
		}

		if (!pc[c].used)
			continue;       // no actual clause content

		++nzclauses;

					// anything which includes symbolic
					// var.names is marked as comment
					// for SAT-designated lines
					//
		if (!in_comment && (STC_R_VSTRING & mode))
			in_comment = sat_start_comment(&fmt);

		for (v=0; v<pc[c].used; ++v) {
			uint64_t cs = offset2cstring(pc[c].soffset[v]) +
			              bytes2cstring(pc[c].sbytes[v]) ;
			size_t offs  = pc[c].soffset[v],
			       bytes = pc[c].sbytes[v];
			char negsign = (mask & signs) ? '-' : 0;
			uint64_t intv = 0;

			if (!is_valid_cstring1(ps, cs))
				return 0;
// TODO: report inconsistent state

			if (STC_R_VNUMBER & mode) {
				intv = sat_varname2int(ps,
					(const char *) &(ps->s.strs[ offs ]),
					bytes);
				if (!intv) {
// SNH: expect all IDs to be already mapped to INTs
					return 0;
				}
			}

			if (!v) {
				if ((STC_R_SATCOMMENT & mode) && !in_comment)
					sat_start_comment(&fmt);
			} else {
				sat_fmt_append1(&fmt, ' ');
			}

			if (STC_R_VSTRING & mode) {
				sat_fmt_append1(&fmt, negsign);
				sat_fmt_append(&fmt, &( ps->s.strs[ offs ] ),
				               bytes);
			}

			if ((STC_R_VSTRING & mode) &&
			    (STC_R_VNUMBER & mode))
				sat_fmt_append1(&fmt, '[');

			if (STC_R_VNUMBER & mode) {
				sat_fmt_append1(&fmt, negsign);
				sat_fmt_append_u64(&fmt, intv);
			}

			if ((STC_R_VSTRING & mode) &&
			    (STC_R_VNUMBER & mode))
				sat_fmt_append1(&fmt, ']');

			mask >>= 1;
		}

		if (STC_R_EMBED & mode)
			printf("%s", STC_REP_PREFIX);

		if (!(STC_R_SATCOMMENT & mode))
			sat_fmt_append(&fmt, " 0", 2);

		printf("%s\n", fmt.s);

		if (c && ((c % 100) == 0))
			fflush(stdout);
	}

	if (!(STC_R_NO_TAIL & mode))
		printf("\n");

	return 1;
}


//--------------------------------------
static size_t cnf_struct2dimacs(char *res, size_t rbytes,
	     const struct SatNumbers *pc) ;


/*----------------------------------------------------------------------------
 * format all registered clauses; output DIMACS
 * numeric-ID equivalent of sat_print_clauses()
 *
 * returns nr. of bytes written; size query with NULL 'res'
 *
 * 'mode' is bitmask, see SatReport_t for bits
 */
static size_t sat_format_int_clauses(void *res,  size_t rbytes,
                    const struct SatState *ps, uint32_t mode)
{
//	unsigned char *pr = (unsigned char *) res;
	size_t wr = 0;

	if (!ps)
		return SAT_SIZET_INVD;

	if (!(STC_R_NOFRAME & mode)) {
		if (STC_R_EMBED & mode) {
			wr = stream_append(res, rbytes, wr,
			            STC_REP_PREFIX, STC_REP_PREFIX_BYTES);
		}

// TODO: append-to-stream macros
			// header: "p cnf <...variables...> <...clauses...>"

		wr += snprintf((void *) ptr_with_offset(res, wr),
		               size_with_offset(rbytes, wr),
		               "p cnf %u %u\n",
		               ps->maxvaridx, ps->n_clauses);
	}

// comments, if we handled them, would come here

	wr = cnf_struct2dimacs((char *) ptr_with_offset(res, wr),
		               size_with_offset(rbytes, wr), &(ps->ns));

	MARK_UNUSED(mode);

	return wr;
}


/*--------------------------------------
 * does not release struct, just anything it references
 */
static void sat_numberrefs_dispose(struct SatNrRefs *pr)
{
	if (pr) {
		free(pr->refs);

		memset(pr, 0, sizeof(*pr));
	}
}


/*--------------------------------------
 * does not release struct, just anything it references
 */
static void sat_numbers_dispose(struct SatNumbers *pn)
{
	if (pn) {
		free(pn->n);

		memset(pn, 0, sizeof(*pn));
	}
}


//--------------------------------------
static void sat_dispose(struct SatState *ps)
{
	if (ps) {
		free(ps->comments.strs);
		free(ps->s.strs);
		free(ps->c);

		sat_numbers_dispose   (&( ps->ns    ));
		sat_numberrefs_dispose(&( ps->crefs ));

		memset(ps, 0, sizeof(*ps));
	}
}

#endif   /*=====  !delimiter: SAT converter  ===============================*/


#if 0   /*=====  delimiter: SAT template-to-CNF converter (v1)  ============*/
//--------------------------------------
static size_t sat_header2mem(void *res,    size_t rbytes,
         const struct SAT_Summary *ps, const char *descr)
{
	size_t wr = 0;

	if (ps && res) {
		wr = snprintf((char *) res, rbytes,
			"p cnf %u %u\n"
			"%s%s%s%s"
			"c\n",
			ps->vars + ps->addl, ps->clauses,
			descr ? "c"   : "",   // note: ASCII ONLY
			descr ? " "   : "",   // note: ASCII ONLY
			descr ? descr : "",
			descr ? "\n"  : "");
	}

	return wr;
}


// we assume there will be one section per primitive
//


//--------------------------------------
// see also sat.py, which can generate the including table entries
//
static const struct CNFTemplate {
	unsigned int bits;     // 1-of-N: this is N (replicated as _INPUT_VARS)
	unsigned int varbits;  // nr. of bits encoding each variable

	                  // masks
	uint32_t mask;    // elem & mask is variable index >0
	uint32_t neg;     // entry is <0
	uint32_t added;   // entry corresponds to added/intermediate varialbe

	unsigned int input_vars;
	unsigned int addl_vars; // first one is overall output
	unsigned int clauses;
	unsigned int maxvars;   // worst-case clause, excl. terminating 0

	const void *table;      // array of uint<...>_t types, see .varbits
	unsigned int elems;
} sat_templ_1ofn[] = {
#if defined(SAT_TEMPL_1_OF_N3_VARBITS)
	SAT_TEMPL_1_OF_N3_FULL,
#endif
#if defined(SAT_TEMPL_1_OF_N4_VARBITS)
	SAT_TEMPL_1_OF_N4_FULL,
#endif
#if defined(SAT_TEMPL_1_OF_N6_VARBITS)
	SAT_TEMPL_1_OF_N6_FULL,
#endif
#if defined(SAT_TEMPL_1_OF_N12_VARBITS)
	SAT_TEMPL_1_OF_N12_FULL,
#endif
#if defined(SAT_TEMPL_1_OF_N16_VARBITS)
	SAT_TEMPL_1_OF_N16_FULL,
#endif
#if defined(SAT_TEMPL_1_OF_N18_VARBITS)
	SAT_TEMPL_1_OF_N18_FULL,
#endif
#if defined(SAT_TEMPL_1_OF_N20_VARBITS)
	SAT_TEMPL_1_OF_N20_FULL,
#endif
#if defined(SAT_TEMPL_1_OF_N24_VARBITS)
	SAT_TEMPL_1_OF_N24_FULL,
#endif
#if defined(SAT_TEMPL_1_OF_N28_VARBITS)
	SAT_TEMPL_1_OF_N28_FULL,
#endif
#if defined(SAT_TEMPL_1_OF_N30_VARBITS)
	SAT_TEMPL_1_OF_N30_FULL,
#endif
#if defined(SAT_TEMPL_1_OF_N32_VARBITS)
	SAT_TEMPL_1_OF_N32_FULL,
#endif
} ;


/*--------------------------------------
 * generators stepping through different-sized uint..._t lists
 */
struct SAT_UList {
	const void *ptr;

	unsigned int unitbytes;

	unsigned int offs;
	unsigned int maxoffs;
} ;
//
#define SAT_ULIST_INIT0  { NULL, 0, 0, 0, }


/*--------------------------------------
 * initialize generator from 'ptempl'
 */
static inline int sat_ulist_init(struct SAT_UList *pu,
                         const struct CNFTemplate *ptempl)
{
	if (!pu || !ptempl || !ptempl->varbits || !ptempl->table ||
	    !ptempl->elems)
		return 0;

// TODO: sane/power-of-two/etc checks

	*pu = (struct SAT_UList) SAT_ULIST_INIT0;

	pu->ptr       =  ptempl->table;
	pu->unitbytes = (ptempl->varbits +7) /8;
	pu->maxoffs   =  ptempl->elems;
				// .off is 0-inited above

	return pu->unitbytes;
}


/*--------------------------------------
 * exhausted stream is reported as invalid
 */
static inline unsigned int is_valid_ulist(const struct SAT_UList *pu)
{
	return (pu && pu->ptr && pu->unitbytes && (pu->offs < pu->maxoffs));
}


/*--------------------------------------
 * returns >0 if 'pu' is still not exhausted after advance
 */
static unsigned int sat_ulist_advance(struct SAT_UList *pu, unsigned int adv)
{
	if (is_valid_ulist(pu))
		pu->offs += adv;

	return is_valid_ulist(pu);
}


/*--------------------------------------
 * does 'pu' contain at least 'adv' unread units?
 *
 * returns >0 if 'pu' is in valid state, not yet at end of input
 *         0  if already exhausted, or state is otherwise invalid
 * result is LS 32 bits of response
 */
static inline uint64_t sat_ulist_current(const struct SAT_UList *pu,
                                                   unsigned int adv)
{
	if (is_valid_ulist(pu) && (pu->offs +adv < pu->maxoffs)) {
		uint64_t rc = UINT64_C(1) << 32;

		switch (pu->unitbytes) {
		case 1:
			return rc | (((const uint8_t *) pu->ptr)
					[ pu->offs +adv ]);

		case 2:
			return rc | (((const uint16_t *) pu->ptr)
					[ pu->offs +adv ]);

		case 4:
			return rc | (((const uint32_t *) pu->ptr)
					[ pu->offs +adv ]);

		default:
			break;
		}
	}

	return 0;
}


//--------------------------------------
static inline
struct SAT_Summary *sat_summary_add(struct SAT_Summary *ps,
                                         unsigned long vars,
                                         unsigned long addl,
                                         unsigned long clauses)
{
	if (ps) {
		ps->vars    += vars;
		ps->addl    += addl;
		ps->clauses += clauses;
	}

	return ps;
}


//--------------------------------------

// fill template from (pt, ptelems)
// inputs bits are (var0, var0 +inputs -1)
// output bit is 'addvar0'
//
// 0 'addvar0' uses variables just after 'var0' (+inputs)
// zero-initializes, then sets non-NULL 'psum'
//
// non-NULL 'maxvar' updated to 1-based index of last referenced variable
//
static size_t sat_1ofn_template2mem(void *res, size_t rbytes,
                      struct SAT_Summary *psum,
                const struct CNFTemplate *pt,
                            unsigned int ptelems,
                            unsigned int inputs,
                            unsigned int var0,
                            unsigned int addvar0)
{
	unsigned int idx = 0, maxidx = 0;
	char *pr = (char *) res;
	size_t wr = 0;

	if (!pr || !rbytes || !pt || !ptelems || !var0)
		return 0;

	sat_summary_init0(psum);

	if (!addvar0) {
		addvar0 = var0 +inputs;
	} else if (var0 +inputs > addvar0) {
		return 0;                   // variable ranges MUST NOT overlap
	}

	while ((idx < ARRAY_ELEMS(sat_templ_1ofn) &&
	       (sat_templ_1ofn[ idx ].bits != inputs)))
		++idx;

	if (idx >= ARRAY_ELEMS(sat_templ_1ofn))
		return 0;

	{
	struct SAT_UList clauses = SAT_ULIST_INIT0;
	uint32_t vmask, neg, is_added;
	unsigned int cls = 0;

	if (!sat_ulist_init(&clauses, &(sat_templ_1ofn[ idx ])))
		return 0;

	sat_ulist_advance(&clauses, CNF_TEMPLATEHDR_ELEMS);
// TODO: cross-check table

	vmask    = sat_templ_1ofn[ idx ].mask;
	neg      = sat_templ_1ofn[ idx ].neg;
	is_added = sat_templ_1ofn[ idx ].added;

	for (cls = 0; sat_templ_1ofn[ idx ].clauses; ++cls) {
		unsigned int currvars = 0, c;
		size_t currwr;

		if (clauses.offs >= clauses.maxoffs)
			break;

		if (!((uint32_t) sat_ulist_current(&clauses, 0)))
			break;              // no variable in clause: early end
// TODO: handle errors, which SNH

		while ((currvars <= sat_templ_1ofn[ idx ].elems) &&
		       ((uint32_t) sat_ulist_current(&clauses, currvars)))
			++currvars;

// TODO: cross-check (max. also in table)

		for (c = 0; c < currvars; ++c) {
			uint32_t var = (uint32_t)sat_ulist_current(&clauses, c);
			int32_t vidx;
					// 'var' was verified as >0 above

			vidx = vmask & var;     // net index, w/o modifier bits

			if (!vidx) {
				// SNH: net variable index MAY NOT be 0
				break;
			}

			vidx += ((is_added & var) ? addvar0 : var0) -1;

			if (maxidx < (uint32_t) vidx)
				maxidx = vidx;

			if (neg & var)
				vidx = -vidx;

			currwr = snprintf(pr +wr, rbytes -wr,
			                  "%s" "%" PRId32,
			                  c ? " " : "", vidx);
// TODO: count remaining buffer

			wr += currwr;
		}
		currwr = snprintf(pr +wr, rbytes -wr, " 0\n");
		wr    += currwr;

		sat_ulist_advance(&clauses, currvars +1);
	}
	}

	if (wr && psum) {
		psum->vars    = maxidx;
		psum->clauses = sat_templ_1ofn[ idx ].clauses;
	}

	return wr;
}


//--------------------------------------
static size_t sat_template(void)
{
	struct SAT_Summary ssum = SAT_SUMMARY_INIT0;
	unsigned char vbits = 12;
	size_t wr = 0;

	if (getenv("BITS"))
		vbits = (unsigned char) cu_readuint(getenv("BITS"), 0);

	wr = sat_1ofn_template2mem(scratch, sizeof(scratch), &ssum,
	                           sat_templ_1ofn, ARRAY_ELEMS(sat_templ_1ofn),
	                           vbits, 1, 0);
	if (wr) {
		unsigned char hdr[ 2048 +1 ] = { 0, };
		size_t hdrb;

		hdrb = snprintf((char *) hdr, sizeof(hdr),
		                "p cnf %u %u\n"
		                "c 1-of-%u (result->%u)\n"
		                "c\n",
		                ssum.vars, ssum.clauses,
		                vbits, vbits +1);

		fwrite(hdr, 1, hdrb, stdout);

		fwrite(scratch, 1, wr, stdout);
	}

	return 0;
}
#endif   /*=====  !delimiter: SAT template-to-CNF converter  ===============*/


/*--------------------------------------
 * see also sat_state_init0(), the typical constructor
 */
static inline
struct SatState *sat_state_add(struct SatState *ps,
                                  unsigned int vars,
                                  unsigned int addl,
                                  unsigned int clauses)
{
	if (ps) {
		ps->vars      += vars;
		ps->addvars   += addl;
		ps->n_clauses += clauses;   // TODO: canonical variable
		sat_update_maxidx(ps);

// TODO: final rules on varidx/add-var-idx stacking
	}

	return ps;
}


//--------------------------------------
static struct SatState *sat_state_init0(struct SatState *ps,
                                           unsigned int inputs)
{
	if (ps) {
		memset(ps, 0, sizeof(*ps));

		ps->vars      = inputs;
		ps->maxvaridx = inputs;
	}

	return ps;
}


/*--------------------------------------
 * number of total elements in worst-case clause collection (across all algs),
 * including any in-band 0 entries, for all clauses of any specific size
 *
 * build-asserted for consistency, see cnf__assertions()
 */
#define  SAT_MAX_CLSS_ELEMS  ((unsigned int) 494)


/* input and additional variables are polymorphic:
 *     non-NULL base[vcount]  -- unsigned int []; index of all inputs
 *         NULL base          -- 1 .. vcount
 *     non-NULL addl[acount]  -- unsigned int []; index of all add'l variables
 *         NULL addl          -- vcount+1 .. vcount+acount
 *
 * note unintuitive combinations of non+NULL input arrays
 */


/*--------------------------------------
 * all clauses for any template, incl. any intermediate 0's terminating clause
 * worst-case size MUST fit all templates
 *
 * expect these to fit the stack on all non-embedded platforms
 */
struct NumericClauses {
	uint32_t vars[ SAT_MAX_CLSS_ELEMS ];
	unsigned int used;
} ;
/**/
#define  SAT_NUM_CLAUSES_INIT0  { { 0, }, 0 }


/*--------------------------------------
 */
struct TemplateBits {
	uint32_t negative;
	uint32_t addl_var;
	uint32_t varmask;
} ;


#if 0
/*--------------------------------------
 * return sign etc. expanded variable from template
 * - base[ vcount ] is list of arbitrary inputs
 * - addl .. addl+acount-1  is list of indirect/added variables (always
 *                          consecutive range)
 *
 * 'tvar' is template variable, incl. any marker bits
 *
 * addl[ acount ] is range of indirect/added variables (always a
 * consecutive range)
 *
 * return index belonging to actual variable reference (not 0)
 *        0     if anything is inconsistent
 */
static int32_t varidx8(const int32_t *base, unsigned int vcount,
                            uint32_t addl,  unsigned int acount,
                            uint32_t tvar,
           const struct TemplateBits *pmarkers)
{
	int32_t rc = 0;

// printf("       .%" PRIx32 " %u\n", tvar, acount);
	if (pmarkers && (tvar & pmarkers->varmask)) {
		unsigned int v = tvar & pmarkers->varmask;              // 1..N

		if (tvar & pmarkers->addl_var) {
			if (v <= acount) {
				rc = addl
				     ? (int32_t) (addl +v -1)
				     : (int32_t) (vcount + v);
			}
// TODO: acount+vcount check: template MUST NOT reference other variables

		} else if (v <= vcount) {
			rc = base ? (int32_t) base[ v-1 ] : (int32_t) v;
		}

		if (rc && (tvar & pmarkers->negative))
			rc = -rc;
// printf("       ? %d\n", (int) rc);
	}

	return rc;
}


//--------------------------------------
static struct TemplateBits unit2markerbits(unsigned int unitbits)
{
	struct TemplateBits tb = { 0, };

	switch (unitbits) {
		case 8:
			tb.negative    = 0x80;
			tb.addl_var    = 0x40;
			tb.varmask     = 0x3f;
			break;
		case 16:
			tb.negative    = 0x8000;
			tb.addl_var    = 0x4000;
			tb.varmask     = 0x3fff;
			break;
		case 32:
			tb.negative    = 0x80000000;
			tb.addl_var    = 0x40000000;
			tb.varmask     = 0x3fffffff;
			break;
	}

	return tb;
}
#endif   // 0


/*--------------------------------------
 * read uint<...>_t sized unit
 *
 * returns ~0 for unsupported configurations, which callers are
 * expected to reject
 */
static inline
uint32_t mem2uint(const void *p, unsigned int offset, unsigned int bits)
{
	switch (p ? bits : 0) {
		case 8: {
			const unsigned char *pc = (const unsigned char *) p;
			return pc[ offset ];
		}

		case 16: {
			const uint16_t *pc = (const uint16_t *) p;
			return pc[ offset ];
		}

		case 32: {
			const uint32_t *pc = (const uint32_t *) p;
			return pc[ offset ];
		}

		default:
			return ~((uint32_t) 0);
	}
}


/*-------------------------------------- 
 * added variables are auto-assigned, from a given base
 * _result_ may be a known variable (such as in a compound operation),
 *
 *
 * V=2, |A|=2, A0=100   (2 inputs, 2 additional variables, start idx is 100)
 *
 * 1  2  3  4  ->  V[0]  V[1]  100  101      if result = 0
 *             ->  V[0]  V[1]  666  100      if result = 666
 */


/*-------------------------------------- 
 * construct int32[] from template and input params
 * result SHOULD fit; callers need to pre-expand. there is a fixed limit,
 * see SAT_MAX_CLSS_ELEMS, and structs defined to contain it.
 *
 * maps vars[] || (result | addl) || addl+1 ... as variables
 *   - 'result' >0 indicates a preallocated result, which is then taken
 *     instead of addl
 *   - further entries follow addl+1...
 *
 * returns 0 if result does not fit, or other error (not a valid template)
 *        _INVD if template is invalid
 *        >0 otherwise: nr. of ints written +1 (we may have empty templates)
 *
 * returns nr. of entries written to start of (res, elems)
 * one of the UINT... errors otherwise
 *
 * 'pa' updated with nr. of clauses added; max(index) of added vars, if non-NULL
 *
 * writes 1-based index of erroneous entry to res[0] upon failure
 */
static unsigned int
sat_template2ints(int32_t *res,    unsigned int elems,
          struct SatAdded *pa,
                const int *templ,  unsigned int tunits,
            const int32_t *vars,   unsigned int vcount,
                  int32_t result,
                 uint32_t addl,    unsigned int acount)
{
	struct SatAdded add = SAT_ADDED_INIT0;
	unsigned int i, wr = 0;

	if (!res || !elems || !templ || !tunits || !vars || !vcount)
		return SAT_UINT_INVD;

	if (acount +vcount < acount)
		return SAT_UINT_INVD;     // sanity check: sane ranges, no wrap
		                          // TODO: document; assert no overflow

	for (i=0; (i < tunits) && ~wr; ++i) {
		int vabs, neg, var = templ[ i ];

		neg  = (var < 0);
		vabs = abs(var);

		if (wr >= elems) {                       // result does not fit
			res[0] = 1+i;
			wr = 0;
			break;

		} else if ((unsigned int) vabs > acount+vcount) {   
				// SNH: template references beyond valid range
			wr = SAT_UINT_INVD;
			res[0] = 1+i;
			break;

		} else if (!vabs) {
			var = 0;           // was already; just mark explicitly
			add.clauses++;

		} else if ((unsigned int) vabs <= vcount) {   // input variable ref
			var = vars[ vabs -1 ];

		} else if (((unsigned int) vabs == vcount+1) && result) {
			var = result;         // added-var: result

		} else {                      // added-variable ref, not result
			var = (vabs - vcount) + addl -1;
			add.addvars = max_uint(var, add.addvars);
		}

		res[ wr ] = neg ? -var : var;
		++wr;
	}

	if (is_valid_unsigned_int(wr)) {
		if (pa)
			*pa = add;
	}

	return wr;
}


#if 0
/*--------------------------------------
 * generalized form of sat_v2template2mem_16() 
 *
 * see cnf_or(), where we replicated the main core
 */
static size_t sat_template2mem8(void *res, size_t rbytes,
                     const uint8_t *ptempl,
                      unsigned int tunits,
                      unsigned int unitbits,
                const unsigned int *base, unsigned int vcount,
                const unsigned int *addl, unsigned int acount)
{
	struct TemplateBits markers = unit2markerbits(8);
	unsigned char *pr = (unsigned char *) res;
	unsigned int i, cls = 0, toffs = 0;
	size_t rv = 0;

	if (!ptempl || (tunits < SAT_TEMPLHDR_UNITS))
		return SAT_SIZET_INVD;

	toffs  += SAT_TEMPLHDR_UNITS;
	tunits -= SAT_TEMPLHDR_UNITS;                  // (tunits) clauses left

	{
	char clstr[ SAT_CLAUSES_ENOUGH_BYTES +1 ] = { 0, };
	size_t cb = 0;

	for (i=0; (i<tunits) && ~cb; ++i) {
		int v, v0 = mem2uint(ptempl, toffs+i, unitbits);
		size_t wr = 0;

// TODO: 666 as fixed addl->...int... replacement
(void) addl;
(void) base;
// TODO: placeholder entry param
		v = varidx8(NULL, vcount, 666, acount, v0, &markers);
						// v == 0  here if clause ends

		wr = snprintf(&(clstr[ cb ]), sizeof(clstr)-cb, "%s" "%d" "%s",
		              cb ? " " : "", v, v ? "" : "\n");

		if (wr >= sizeof(clstr) -cb) {                   // did not fit
			rv = SAT_SIZET_INVD;
			break;
		}
		cb += wr;

// TODO: memmove()-based in-stream append
// printf("END[%zu]=(%s)\n", cb, (const char *) clstr);
//			printf("CLAUSE[%u]=(%s)\n", cls+1, clstr);

		if (!v) {
			if (pr) {
				if (cb <= rbytes - rv) {
					memmove(pr+rv, clstr, cb);
					if (rv+cb < rbytes)
						pr[ rv+cb ] = '\0';
					rv += cb;
				} else {
					rv = SAT_SIZET_INVD;
					break;
				}
			}
			cb = 0;
			++cls;
		}
	}
	}

	return rv;
}
#endif


//--------------------------------------
// generic table-assisted template-to-CNF(text) conversion
//   generalized from sat_1ofn_template2mem()
//
// uint...UNITBITS_t templ[ tunits ]
//
// 'idx' selects 0-based entry from 'tidx' which references templ[]
//
static size_t sat_template_arr2mem(void *res,    size_t rbytes,
                  struct NumericClauses *pn,
                     struct SAT_Summary *psum,
                           unsigned int idx,
                const struct TemplIndex *tidx, unsigned int tielems,
                             const void *templ,  size_t tunits,
                           unsigned int unitbits)
{
(void) res;
(void) rbytes;
	if (!tidx || !tielems || !templ || !tunits || !pn)
		return 0;

	*pn = (struct NumericClauses) SAT_NUM_CLAUSES_INIT0;

	if (unitbits != 8)
		return 0;

	if (idx >= tielems)
		return 0;

	sat_summary_init0(psum);

// RRR

	return 0;
}


#if 0   /*=====  delimiter: SAT template-to-CNF converter (v2)  ============*/
#include "1ofn-n128-v2template.c"

/* condensed, v2 templates:
 *
 * #define  SAT_TMPL_..._VAR_IS_NEGATED  UINT16_C (0x8000)
 * #define  SAT_TMPL_..._VAR_IS_CLAUSE_END  UINT16_C (0x4000)
 * #define  SAT_TMPL_..._VAR_IS_ADDED    UINT16_C (0x2000)
 * #define  SAT_TMPL_..._VAR_MASK        UINT16_C (0x1fff)
 * #define  SAT_TMPL_..._MAX_VARS        ((unsigned int) 128)
 * #define  SAT_TMPL_..._MAX_ADDL_VARS   ((unsigned int)  41)
 * #define  SAT_TMPL_..._MAX_CLAUSES     ((unsigned int) 342)
 * #define  SAT_TMPL_..._MAX_VARS_PER_CLAUSE  ((unsigned int) 5)
 *
 * static const uint16_t SAT_TMPL_1OFN_templates[50082] = {
 *     0x0080,0x0029,0x0005,0x0156,    header: max 128(x80) inputs,
 *                                      41(x29) additional variables,
 *                                      5 variables per clause,
 *                                      342 clauses per template
 *
 *     0x0001,0x0000,0x0001,0x0001,    // 1+0 vars, 1 cls, nr.vars<=1/cls
 * [1] ->
 *         0x4001,
 *         ^^^^^^ SAT_TMPL_..._VAR_IS_CLAUSE_END | 1
 *
 *     0x0002,0x0001,0x0004,0x0003,    // 2+1 vars, 4 cls, nr.vars<=3/cls
 * [1, 2, -3], [-1, 2, 3], [1, -2, 3], [-1, -2, -3], [3] ->
 *  2+1 vars -> 1 -> 1, 2 -> 2 (original variables); 3 -> 1 (+variable)
 *
 *         [1,    2,     -3]     [-1,   2,     3]      [1,    -2,    3]
 *         0x0001,0x0002,0xe001, 0x8001,0x0002,0x6001, 0x0001,0x8002,0x6001, ...
 *                       ^^^^^^ SAT_TMPL_..._VAR_IS_NEGATED |
 *                              SAT_TMPL_..._VAR_IS_CLAUSE_END | 1 ->
 *                              additional variable (1) -> global (3)
 * ...
 * } ;
 *
 *
 * // index list
 * static const struct {
 *      unsigned int offset;
 *      unsigned int count;
 * } SAT_TMPL_1OFN_INDEX[128] = {
 *      {     4,   9 },       note: 1-based; starting table header not indexed
 *      {     9,  16 },
 *      {    25,  20 },
 * ...
 * } ;
 */


/*--------------------------------------
 * does 1-based 'idx' point to a proper value in (tindex, tcount),
 * within a 'template_units'-sized array?
 *
 * if so, return offset of 1st unit, and nr. in 'units'
 *               SAT_UINT_INVD any error; any size over 'templ_units' is error
 *
 * templates start with SAT_TEMPLHDR_UNITS of limits; always
 * returns >= units
 */
static unsigned int template2index(unsigned int *units,
                        const struct TemplIndex *tindex, unsigned int icount,
                                   unsigned int templ_units,
                                   unsigned int idx)
{
	unsigned int offs, u;

	if (units)
		*units = 0;

	if (!tindex || !idx || (idx > icount))
		return SAT_UINT_INVD;

// TODO: report 'insufficient table entries'

	offs = tindex[ idx -1 ].offset;
	u    = tindex[ idx -1 ].count;

	if (u < SAT_TEMPLHDR_UNITS)
		return SAT_UINT_INVD;               // table inconsistent (SNH)

	if ((offs >= templ_units) || (offs +u > templ_units))
		return SAT_UINT_INVD;                   // table overflow (SNH)

	if (units)
		*units = u;

	return offs;
}


/*--------------------------------------
 * non-NULL 'tindex' implies picking up template from packed one,
 * using var0 as 1-based index into [tindex, icount]
 */
static size_t sat_v2template2mem_16(void *res, size_t rbytes,
                              const void *template, unsigned int tcount,
                 const struct TemplIndex *tindex,   unsigned int icount,
                            unsigned int var0,
                            unsigned int addvar0)
{
	const uint16_t *pt = (const uint16_t *) template;
	unsigned int i, cls = 0;

	if (!rbytes || !template || !tcount)
		return 0;

	if (tindex) {
		unsigned int offs = template2index(&tcount, tindex, icount,
		                                   tcount, var0);
		if (offs == SAT_UINT_INVD)
			return SAT_SIZET_INVD;
		pt += offs;
				// tcount updated above; (pt, tcount) is table
	}
	if (tcount < SAT_TEMPLHDR_UNITS)
		return SAT_SIZET_INVD;

	pt     += SAT_TEMPLHDR_UNITS;
	tcount -= SAT_TEMPLHDR_UNITS;           // (pt, tcount) are all clauses

	{
	char clause[ 1024 +1 ] = { 0, };
	size_t cb = 0;

	for (i=0; i<tcount; ++i) {
		int v = pt[i] & SAT_TMPL_1OFN_VAR_MASK;

		if (pt[i] & SAT_TMPL_1OFN_VAR_IS_ADDED)
			v += addvar0;

		if (pt[i] & SAT_TMPL_1OFN_VAR_IS_NEGATED)
			v = -v;

//		printf("  [%u/%u]x%" PRIx16 "\n", i, tcount, pt[i]);

		cb += snprintf(&(clause[cb]), sizeof(clause), "%s%d",
		               cb ? " " : "", v);

		if (pt[i] & SAT_TMPL_1OFN_VAR_IS_CLAUSE_END) {
			cb += snprintf(&(clause[cb]), sizeof(clause), " 0");

//			printf("CLAUSE[%u]=(%s)\n", cls+1, clause);

			cb = 0;
			++cls;
		}
	}
	}
printf("\n");

(void) res;
	return 0;
}


//--------------------------------------
static size_t sat_v2template2mem(void *res,        size_t rbytes,
                           const void *template, unsigned int tcount,
              const struct TemplIndex *tindex,   unsigned int icount,
                         unsigned int unitbits,
                         unsigned int var0,
                         unsigned int addvar0)
{
	switch ((template && tcount) ? unitbits : 0) {
	case 16:
		return sat_v2template2mem_16(res, rbytes, template, tcount,
		                             tindex, icount, var0, addvar0);
	default:
		return 0;
	}
}
#endif   /*=====  !delimiter: SAT template-to-CNF converter  ===============*/


#if 2   /*=====  delimiter: CNF-constructor library functions  =============*/
// these are the rough equivalents of sat_or() etc., constructing directly
// to output buffers
//
// replacing dedicated AND/OR constructions with generic template-to-X
// conversion

// any offline global limit etc. comparison would come here
static inline void cnf__assertions(void)
{
#if defined(CNF_OR_MAX_ELEMS__)
	BUILD_ASSERT(CNF_OR_MAX_ELEMS__ <= SAT_MAX_CLSS_ELEMS);
#endif

#if defined(CNF_AND_MAX_ELEMS__)
	BUILD_ASSERT(CNF_AND_MAX_ELEMS__ <= SAT_MAX_CLSS_ELEMS);
#endif

#if defined(CNF_NEQ0_MAX_ELEMS__)
	BUILD_ASSERT(CNF_NEQ0_MAX_ELEMS__ <= SAT_MAX_CLSS_ELEMS);
#endif

#if defined(CNF_LT_MAX_ELEMS)
	BUILD_ASSERT(CNF_LT_MAX_ELEMS <= SAT_MAX_CLSS_ELEMS);
#endif

#if defined(CNF_1OFN_MAX_ELEMS)
	BUILD_ASSERT(CNF_1OFN_MAX_ELEMS <= SAT_MAX_CLSS_ELEMS);
#endif
}


/*--------------------------------------
 * checks that nr. of units is header-clean
 */
static int is_valid_cnf_templ_index(const struct TemplIndex *pi)
{
	return (pi && (pi->offset | pi->count) &&
	        (pi->count >= SAT_TEMPLHDR_UNITS));
}


/*--------------------------------------
 * does index 'n' make sense for the (pi, count) table?  if so,
 * return a valid TemplIndex entry
 *
 * 'base' is minimal index which makes sense; corresponds to [0]
 */
static struct TemplIndex
cnf_table2template(const struct TemplIndex *pi, unsigned int count,
                              unsigned int n,
                              unsigned int base)
{
	struct TemplIndex ix = CNF_TEMPLIDX_INIT0;

	if (pi && count && (n >= base) && ((n -base) < count))
		ix = pi[ n -base ];

	return ix;
}


/*--------------------------------------
 * NULL/inconsistent/etc. input reported as 'not within'
 * returns 1-based index into arr[] if valid
 *
 * since we measure tables in units, no 8/16/32-bit polymorphism needed
 */
static int is_within_array(const void *arr, unsigned int units,
              const struct TemplIndex *pt)
{
	if (!arr || !units || !pt)
		return 0;

	if ((pt->offset >= units) || ((pt->offset + pt->count) > units))
		return 0;

	return 1 + pt->offset;
}


/*--------------------------------------
 * note: we do not (yet?) cover minimal-template check (-> unit count) here
 */
static inline int valid_template_vars(const struct SAT_Summary *ps)
{
	return (ps && ps->vars);
}


//--------------------------------------
static void report_template_vars(const struct SAT_Summary *ps)
{
	if (valid_template_vars(ps)) {
		printf("SAT: %u inputs, +%u variables, %u clauses\n",
		       ps->vars,
		       ps->addl,
		       ps->clauses);
	}
}


//--------------------------------------
static void report_template_additions(const struct SatAdded *pa)
{
	if (pa) {
		printf("SAT: +%u variables, +%u clauses\n",
		       pa->addvars,
		       pa->clauses);
	}
}

//--------------------------------------
static void report_sat_state(const char *msg, const struct SatState *ps)
{
	if (ps) {
		if (msg)
			printf("%s\n", msg);

		printf("SAT: %u inputs, +%u variables, %u clauses "
			"(%u numeric); %u/%u nrs used\n",
		       ps->vars,
		       ps->addvars,
		       ps->c_used,
		       ps->n_clauses,
		       ps->ns.used,
		       ps->ns.allocd);
	}
}


//--------------------------------------
static void report_conversion_state(const struct SatConvert *pc)
{
	if (pc) {
		printf("SAT conversion\n");
		report_template_additions(&( pc->add ));

		printf("template: %u,%u\n", pc->ix.offset, pc->ix.count);
	}
}


/*--------------------------------------
 * register 'result' as output [possibly, as one of several]
 *
 * returns 0 if anything inconsistent (struct missing, or already registered
 * conflicting/too many results)
 */
static unsigned int sat_add_result(struct SatAdded *pa, uint32_t response)
{
	BUILD_ASSERT(ARRAY_ELEMS(pa->result) == 1);

	if (pa && response) {
		if (!pa->rvars ||
		    ((pa->rvars == 1) && (pa->result[0] == response)))
		{
			pa->result[0] = response;
			pa->rvars     = 1;

			return pa->rvars;
		}
	}

	return 0;
}


/*--------------------------------------
 * expand numeric list into DIMACS CNF-clause form to start of (res, rbytes)
 *
 * returns written byte count, or one of SIZET_E... constants
 * TODO: use placeholder array; count size with NULL 'res'
 */
static size_t cnf_struct2dimacs(char *res, size_t rbytes,
	     const struct SatNumbers *pc)
{
	size_t wr = 0;

	if (pc && res && rbytes) {
		unsigned int i, line_start = 1;

// TODO: pick direct write-to-stream macros
// TODO: sync format-to-something macros, since there are several partial ones
		for (i=0; i<pc->used; ++i) {
			int curr, v = pc->n[i];

			curr = snprintf(&(res[ wr ]), rbytes - wr, 
			           "%s" "%d" "%s",
			           line_start ? "" : " ",
			           v,
			           v ? "" : "\n");
// TODO: auto-terminate (even if we 0-pad each clause)

			if ((size_t) curr >= rbytes-wr) {       // does not fit
				wr = SAT_SIZET_ETOOSMALL;
				break;
			}
			wr += curr;

			line_start = !v;
		}
	}

	return wr;
}
	                            // .used includes clause-terminating 00's


/*--------------------------------------
 * returns NULL for any error, incl. allocated-but-full structs
 */
static int32_t *sat_nrs_1st_unused(const struct SatNumbers *pn)
{
	return (pn && pn->n && (pn->used < pn->allocd))
	        ? &(pn->n[ pn->used ]) : NULL ;
}


//--------------------------------------
static unsigned int sat_nrs_unused_count(const struct SatNumbers *pn)
{
	return (pn && pn->n && (pn->used < pn->allocd))
	        ? (pn->allocd - pn->used) : 0 ;
}


//--------------------------------------
static struct SAT_Summary templ2vars(const void *templ, unsigned int units,
                                   unsigned int unitbits) ;

static struct SAT_Summary inttempl2vars(const int *templ, unsigned int units) ;

/*--------------------------------------
 * retrieve and sanity-check template-index entry
 * !is_valid_cnf_templ_index( ...returned entry... ) if anything fails
 *
 * (pi, count) is table; 'n' is current index, 'base' is first index
 * which makes sense for this table
 */
static struct TemplIndex sat_table2idx(const struct TemplIndex *pi,
                                                  unsigned int count,
                                                  unsigned int n,
                                                  unsigned int base)
{
	struct TemplIndex ix = CNF_TEMPLIDX_INIT0;

	ix = cnf_table2template(pi, count, n, base);

	if (is_valid_cnf_templ_index(&ix)) {
		if (ix.count <= SAT_TEMPLHDR_UNITS)
			ix = (struct TemplIndex) CNF_TEMPLIDX_INIT0;
	}

	return ix;
}


/*--------------------------------------
 * common primitive: pick up template for a size-selected instance
 * of an operation
 *
 * sets *pc to struct describing additions (variables etc.) without
 * updating *ps
 *
 * pc->ix points to net clause list within tints[], already stripped
 * away entry header
 *
 * 'tints'    int[] list of clauses
 * 'pix'      index into 'tints'
 * 'vcount'   number of input variables
 * 'base'     lowest reasonable 'vcount'
 * 'maxelems' worst-case limit of elements used by all claues, incl.
 *            0-terminating entries
 */
static
size_t template2entry(struct SatState *ps,
                    struct SatConvert *pc,
              const struct TemplIndex *pix,   unsigned int ixcount,
                            const int *tints, unsigned int ticount,
                         unsigned int vcount, unsigned int base,
                         unsigned int maxelems)
{
	if (!valid_sat_params(ps) || !pc || !pix || !ixcount)
		return 0;

	*pc = (struct SatConvert) SAT_CONVERT_INIT0;

	pc->ix = sat_table2idx(pix, ixcount, vcount, base);

	if (!is_valid_cnf_templ_index(&( pc->ix )))
		return cu_reportrc("template/index range", SAT_SIZET_ECOUNT);

	if (!is_within_array(tints, ticount, &( pc->ix )))
		return cu_reportrc("SNH: bad templ/entry", SAT_SIZET_EINTERN);

// TODO: centralized macro; centralized empty-template handling

	if (pc->ix.count == SAT_TEMPLHDR_UNITS)
		return 1;

	pc->vars = inttempl2vars(&(tints[ pc->ix.offset ]), pc->ix.count);

	if (!valid_template_vars(&( pc->vars )))
		return cu_reportrc("SNH: bad template/vars", SAT_SIZET_EINTERN);

// TODO: replicated fields -> merge/deduplicate
	pc->add.addvars = pc->vars.addl;
	pc->add.clauses = pc->vars.clauses;

	pc->ix.offset += SAT_TEMPLHDR_UNITS;
	pc->ix.count  -= SAT_TEMPLHDR_UNITS;         // net clauses, w/o header

	if (sat_ensure_numbers(ps, maxelems) <0)
		return SAT_SIZET_ENOMEM;

	return 1;
}


/*--------------------------------------
 * recurring template-to-clause.list construction:
 *
 * size_t cnf_...(struct SatState *ps,   -- updated global state
 *                struct SatAdded *pa,   -- additions in this set of clauses
 *                       uint32_t ret,   -- ret. value (index), if known
 *                                       -- TODO: do we ever use negated 'ret'?
 *                  const int32_t *a, unsigned int an,
 *                                       -- inputs are a[an]
 *                   unsigned int flags) ;
 */


/*--------------------------------------
 * append template of OR(..a[]..) to numeric-clauses list of 'ps'
 *
 * 'pa'   updated with full addition context if non-NULL
 * 'rvar' updated with OR() variable index (>0) if non-NULL
 * 'ret'  is variable to use if not 0; MUST be already available/reserved
 */
static
size_t cnf_or(struct SatState *ps,
              struct SatAdded *pa,
                     uint32_t ret,
                const int32_t *a, unsigned int an,
                 unsigned int flags)
{
	struct SatConvert cv = SAT_CONVERT_INIT0;
	struct SatAdded add  = SAT_ADDED_INIT0;
	unsigned int c;
	size_t te;

	(void) cnf__assertions();              // reference otherwise-unused fn

	if (!valid_sat_params(ps) || !a)
		return 0;

	te = template2entry(ps, &cv, ARRAY_OF(cnf_or_templ_ints_idx),
	                    ARRAY_OF(cnf_or_template_ints), an, 1,
	                    CNF_OR_MAX_ELEMS__);
	if (te && is_valid_sat_size(te)) {
		ret = sat_register_news(ps, &(cv.add), ret);
		if (!ret)
			te = SAT_SIZET_ENOMEM;
	}
	if (!te || !is_valid_sat_size(te))
		return te;

	c = sat_template2ints(SAT_NR_UNUSED(&( ps->ns )), &add,
	                      &(cnf_or_template_ints[ cv.ix.offset ]),
	                      cv.ix.count, a, an, ret,
	                      sat_next_var_index(ps), cv.add.addvars);
	if (is_valid_unsigned_int(c))
		ps->ns.used += c;

// ...rest...
(void) flags;

	if (pa)
		*pa = cv.add;

	return 1;
}


/*--------------------------------------
 * append template of OR(..a[]..) to numeric-clauses list of 'ps'
 *
 * 'pa'   updated with full addition context if non-NULL
 * 'rvar' updated with OR() variable index (>0) if non-NULL
 * 'ret'  is variable to use if not 0; MUST be already available/reserved
 */
static
size_t cnf_and(struct SatState *ps,
               struct SatAdded *pa,
                      uint32_t ret,
                 const int32_t *a, unsigned int an,
                  unsigned int flags)
{
	struct SatConvert cv = SAT_CONVERT_INIT0;
	struct SatAdded add  = SAT_ADDED_INIT0;
	unsigned int c;
	size_t te;

	if (!valid_sat_params(ps) || !a)
		return 0;

	te = template2entry(ps, &cv, ARRAY_OF(cnf_and_templ_ints_idx),
	                    ARRAY_OF(cnf_and_template_ints), an, 2,
	                    CNF_AND_MAX_ELEMS__);
	if (te && is_valid_sat_size(te)) {
		ret = sat_register_news(ps, &(cv.add), ret);
		if (!ret)
			te = SAT_SIZET_ENOMEM;
	}
	if (!te || !is_valid_sat_size(te))
		return te;

// TODO: proper non-redundant accounting; then dispose
ps->addvars--;
ps->maxvaridx--;
sat_update_maxidx(ps);

	c = sat_template2ints(SAT_NR_UNUSED(&( ps->ns )), &add,
	                      &(cnf_and_template_ints[ cv.ix.offset ]),
	                      cv.ix.count, a, an, ret,
	                      sat_next_var_index(ps), cv.add.addvars);
// ...process add...

	if (is_valid_unsigned_int(c))
		ps->ns.used += c;

// ...rest...
(void) flags;

	if (pa)
		*pa = cv.add;

	return 1;
}


/*--------------------------------------
 * append template of 1-of-N(..a[]..) to numeric-clauses list of 'ps'
 *
 * 'pa'   updated with full addition context if non-NULL
 * 'rvar' updated with OR() variable index (>0) if non-NULL
 *
 * 'ret'  is unused: we only use forced-1-of-N relationships, and do
 *        not need to return anything. (our templates already incorporate
 *        the understanding that the global result is True.)
 */
static
size_t cnf_1ofn(struct SatState *ps,
                struct SatAdded *pa,
                       uint32_t ret,
                  const int32_t *a, unsigned int an,
                   unsigned int flags)
{
	struct SatConvert cv = SAT_CONVERT_INIT0;
	struct SatAdded add  = SAT_ADDED_INIT0;
	unsigned int c, addbase;
	size_t te;

	if (!valid_sat_params(ps) || !a)
		return 0;

	te = template2entry(ps, &cv, ARRAY_OF(cnf_1ofn_templ_ints_idx),
	                    ARRAY_OF(cnf_1ofn_template_ints), an, 1,
	                    CNF_OR_MAX_ELEMS__);
	if (!te || !is_valid_sat_size(te))
		return te;

// TODO: simplify stacking -> remove call-through fns
	sat_register_additions(ps, &(cv.add));
	addbase = ps->vars +1; 
	ret = 0;                                          // note: no ret.value

	c = sat_template2ints(SAT_NR_UNUSED(&( ps->ns )), &add,
	                      &(cnf_1ofn_template_ints[ cv.ix.offset ]),
	                      cv.ix.count, a, an, ret,
	                      addbase, cv.add.addvars);
// ...process add...
	if (is_valid_unsigned_int(c))
		ps->ns.used += c;

// ...rest...
(void) flags;

	if (pa)
		*pa = cv.add;

	return 1;
}


#endif   /*=====  !delimiter: CNF-constructor library functions  ===========*/


#if defined(CNF_LT_TEMPLATE_H__)  //=========================================
struct SatVariables {
	unsigned int vars;
	unsigned int addl;
} ;
//
#define  SAT_VARIABLES_INIT0  { 0, 0 }


#if 0
// TODO: proper stream-append version
// right now, assumes fixed 'large enough' 'descr'
//
static size_t describe_runs(void *descr, size_t dbytes,
                    unsigned int limit)
{
	unsigned int curr, prev, seen = 0;
	char *pd = (char *) descr;
	size_t wr = 0;

// TODO: generic ls-zeroes() macro
	if (limit >= 0x100) {
		curr = 0x8000;
	} else {
		curr = 0x80;
	}
	while (curr > limit)
		curr >>= 1;

	prev = limit & curr;

	if (descr && (wr+1 < dbytes)) {
		pd[ wr   ] = 'b';
		pd[ wr+1 ] = ':';
	}
	wr += 2;

	while (curr) {
		if (((!prev) != !(curr & limit))) {
			if (descr && (wr < dbytes))
				pd[ wr ] = '-';
			++wr;
			seen = 0;
		}

		prev = curr & limit;

		if ((seen >3) && !(seen % 4)) {
			if (descr && (wr < dbytes))
				pd[ wr ] = '\'';
			++wr;
		}

		if (descr && (wr < dbytes))
			pd[ wr ] = prev ? '1' : '0';
		++wr;
		++seen;

		curr >>= 1;
	}

	if (descr && (wr < dbytes))
		pd[ wr ] = 0;

	return wr;
}
#endif


//--------------------------------------
static struct SAT_Summary inttempl2vars(const int *templ, unsigned int units)
{
	struct SAT_Summary rv = SAT_SUMMARY_INIT0;

	if (templ && (units >= SAT_TEMPLTABLE_HDR_UNITS)) {
		rv.vars     = templ[0];
		rv.addl     = templ[1];
		rv.clauses  = templ[2];
		rv.maxcvars = templ[3];
	}

	return rv;
}


//--------------------------------------
static struct SAT_Summary templ2vars(const void *templ, unsigned int units,
                                   unsigned int unitbits)
{
	struct SAT_Summary rv = SAT_SUMMARY_INIT0;
	unsigned int v = 0, a, c;                     // v>0 if struct is valid

	switch ((templ && (units >= SAT_TEMPLTABLE_HDR_UNITS)) ? unitbits : 0)
	{
		case 8: {
			const unsigned char *pt = (const unsigned char *) templ;
			v = pt[0];
			a = pt[1];
			c = pt[2];
			break;
		}

		case 16: {
			const uint16_t *pt = (const uint16_t *) templ;
			v = pt[0];
			a = pt[1];
			c = pt[2];
			break;
		}

		case 32: {
			const uint32_t *pt = (const uint32_t *) templ;
			v = pt[0];
			a = pt[1];
			c = pt[2];
			break;
		}

		default:
			break;
	}

	if (v) {
		rv.vars    = v;
		rv.addl    = a;
		rv.clauses = c;
	}

	return rv;
}
#endif    //=================================================================


//----------------------------------------------------------------------------
int main(int argc, char **argv)
{
	const char *hostname = (argc > 1) ? argv[1] : "localhost";
	int port = (argc > 2) ? atoi(argv[2]) : 6379;
	struct SatState psat;
	struct PNR_DB db;
	int rc = -1;

	memset(&db,   0, sizeof(db));
	memset(&psat, 0, sizeof(psat));

	if (0) {            // reference static fns
		imh_append(NULL, NULL, NULL, ~0);
		imh_idx(NULL, ~0);
		imh_entry(NULL, ~0);
		imh_main_dispose();

		report_conversion_state(NULL);
		report_sat_state(NULL, NULL);
		report_template_vars(NULL);
		sat_next_var(NULL);
		sat_1ofn_prod(NULL, NULL, 0, NULL, ~0, 0);
		sat_template_arr2mem(NULL, 0, NULL, NULL, 0, NULL, ~0,
		                     NULL, ~0, 0);
		sat_ensure_numrefs(NULL, ~0);
	}

{
unsigned int mni = 1, mxi = ARRAY_ELEMS(cnf_1ofn_templ_ints_idx), i;
struct SatAdded add;
int32_t a[64];
size_t wr;

for (i=0; i<ARRAY_ELEMS(a); ++i)
	a[i] = 1+i;

if (getenv("OR")) {
	cnf_or(&psat, &add, 666, a, 6, 0);
	cnf_or(&psat, &add, 0, &(a[6]), 10, 0);

	wr = sat_format_int_clauses(scratch, sizeof(scratch), &psat, 0);
	if (!is_valid_sat_size(wr))
		return -1;

	printf("## DIMACS[OR]\n");
	printf("%s", scratch);
	return 0;
}

if (getenv("BITS")) {
	mni = (unsigned char) cu_readuint(getenv("BITS"), 0);
	mxi = mni;
}

for (i=mni; i<=mxi; ++i) {
	sat_state_init0(&psat, i);

//	cnf_1ofn(&psat, &add, 0, a, i, 0);
	cnf_and(&psat, &add, 0, a, i, 0);

	wr = sat_format_int_clauses(scratch, sizeof(scratch), &psat, 0);
	if (!is_valid_sat_size(wr))
		continue;

	printf("## DIMACS[1-of-%u]\n", i);
	printf("%s", scratch);
}

return 0;
}

#if 0 && defined(CNF_LT_TEMPLATE_H__) && defined(CNF_NEQ0_TEMPLATE_H__)
	if (getenv("TEMPLATE_LT") || getenv("TEMPLATE_NEQ0")) {
		char descr[ 256 +1 ] = { 0, };
		unsigned int limit, tmplsizes;
		struct SAT_Summary vars;
		struct TemplIndex idx;
		uint64_t rv;
		size_t wr;

		rv = getenv("TEMPLATE_LT")
		     ? cu_readuint(getenv("TEMPLATE_LT"),   0)
		     : cu_readuint(getenv("TEMPLATE_NEQ0"), 0);
		/**/
		if (rv == CU_INVD_UINT64)
			return cu_reportrc("invalid LT/template", -1);

				// 1-based index into array-of-templates
		tmplsizes = getenv("TEMPLATE_LT")
		            ? ARRAY_ELEMS(cnf_lt_templ_idx)
		            : ARRAY_ELEMS(cnf_neq0_templ_idx) ;

		if (!rv || (rv > tmplsizes))
			return cu_reportrc("template/index out of range", -1);
		limit = rv;

		idx = getenv("TEMPLATE_LT")
		      ? cnf_lt_templ_idx  [ limit-1 ]
		      : cnf_neq0_templ_idx[ limit-1 ];

		if (getenv("TEMPLATE_LT")) {
			if (!is_within_array(cnf_lt_template_bin,
			         ARRAY_ELEMS(cnf_lt_template_bin), &idx))
				return cu_reportrc("SNH: bad templ/entry", -1);

			vars = templ2vars(&(cnf_lt_template_bin[ idx.offset ]),
			                    idx.count, 8);
		} else {
			if (!is_within_array(cnf_neq0_template_bin,
			         ARRAY_ELEMS(cnf_neq0_template_bin), &idx))
				return cu_reportrc("SNH: bad templ/entry", -1);

// TODO: generic, uint-width-independent form
			vars = templ2vars(&(cnf_neq0_template_bin[ idx.offset ]),
			                    idx.count, 8);
		}

		if (!valid_template_vars(&vars))
			return cu_reportrc("SNH: invalid template/vars", -1);

{
char rdescr[ 128 +1 ] = { 0, };
const char *what;

describe_runs(rdescr, sizeof(rdescr), limit);

what = getenv("TEMPLATE_LT") ? "LESS-THAN" : "NEQ-OR0" ;

snprintf(descr, sizeof(descr), "%s(%u/x%04x/%s)->v%u",
	what, limit, limit, rdescr, vars.vars+1);
}
		wr =  sat_header2mem(scratch, sizeof(scratch), &vars, descr);

	if (getenv("TEMPLATE_LT")) {
		wr += sat_template2mem8(&(scratch[ wr ]), sizeof(scratch)-wr,
		         &(cnf_lt_template_bin[ idx.offset ]), idx.count, 8,
		         NULL, vars.vars, NULL, vars.addl);
	} else {
		wr += sat_template2mem8(&(scratch[ wr ]), sizeof(scratch)-wr,
		         &(cnf_neq0_template_bin[ idx.offset ]), idx.count, 8,
		         NULL, vars.vars, NULL, vars.addl);
	}
if (is_valid_sat_size(wr))
	printf("%s", scratch);
return 0;
	}
#endif    // CNF templates included

#if 0
	{
	sat_v2template2mem(NULL, ~0, SAT_TMPL_1OFN_templates,
	               ARRAY_ELEMS(SAT_TMPL_1OFN_templates),
	               SAT_TMPL_1OFN_INDEX, ARRAY_ELEMS(SAT_TMPL_1OFN_INDEX),
	               16, 8, 8);

	sat_v2template2mem(NULL, ~0, SAT_TMPL_1OFN_templates,
	               ARRAY_ELEMS(SAT_TMPL_1OFN_templates),
	               SAT_TMPL_1OFN_INDEX, ARRAY_ELEMS(SAT_TMPL_1OFN_INDEX),
	               16, 12, 9);

	sat_v2template2mem(NULL, ~0, SAT_TMPL_1OFN_templates,
	               ARRAY_ELEMS(SAT_TMPL_1OFN_templates),
	               SAT_TMPL_1OFN_INDEX, ARRAY_ELEMS(SAT_TMPL_1OFN_INDEX),
	               16, 128, 41);
	return 0;
	}
#endif

#if 0 && defined(CNF_TEMPLATES_H__)
	if (1) {
		sat_template();
		return 0;
	}
#endif

	do {
#if !defined(SYS_NO_REDIS)
	db.rd.ctx = rds_open(hostname, port);
	if (!db.rd.ctx)
		return -1;

	if (rds_hash0(db.rd.ctx, HSH_MAINHASH) <0)
		break;
	if (rds_hash0(db.rd.ctx, HSH_ADDLHASH) <0)
		break;

	psat.db = db;
#endif
#if !defined(SYS_NO_LMDB)
	if (lmd_hash0(&(db.lm.henv), &(db.lm.hdbi), HSH_MAINHASH) <0)
		break;
	if (lmd_hash0(&(db.lm.aenv), &(db.lm.adbi), HSH_ADDLHASH) <0)
		break;
#endif

	{
	uint64_t a, b, c, d, e0, f1, r;
	uint64_t varr[ 25600 ] = { 0, }; // arrays of variables for 1-of-N tests
	unsigned int i, j;

	a  = sat_name2cs(&psat, "d1t1",    4, HSH_MAINHASH);
	b  = sat_name2cs(&psat, "d2t3",    4, HSH_MAINHASH);
	c  = sat_name2cs(&psat, "d3t8",    4, HSH_MAINHASH);
	d  = sat_name2cs(&psat, "d4t9",    4, HSH_MAINHASH);
	e0 = sat_name2cs(&psat, "efixed0", 7, HSH_MAINHASH);
	f1 = sat_name2cs(&psat, "ffixed1", 7, HSH_MAINHASH);
	r  = sat_name2cs(&psat, "NV1",     3, HSH_ADDLHASH);

	sat_xor1(NULL, &psat, r, a, b, 0);

	{
	char tmpname[ 32 +1 ] = { 0, };

if (0) {
	for (i=0; i<ARRAY_ELEMS(varr); ++i) {
		size_t wr;

		wr = snprintf(tmpname, sizeof(tmpname), "d999t%04u", i);

		varr[i] = sat_name2cs(&psat, tmpname, wr, HSH_MAINHASH);
		if (!varr[i])
			return -1;
	}
}
	}

	{
	uint64_t arr[6] = { a, b, c, d, e0, f1 };
	struct SatName nn;

	sat_neq_or0(&nn, &psat, 0, arr, 3, &(arr[3]));

if (0) {
	sat_xor1(&nn, &psat, 0, c, d, 0);
	sat_xor1(&nn, &psat, 0, a, c, 1);

	sat_or(NULL, &psat, r, arr, ARRAY_ELEMS(arr), 0);
	sat_or(NULL, &psat, r, arr, ARRAY_ELEMS(arr), SAT_FL_INVERT);
	sat_or(&nn, &psat, 0, arr, ARRAY_ELEMS(arr), 0);
	sat_or(&nn, &psat, 0, arr, ARRAY_ELEMS(arr), SAT_FL_INVERT);

	sat_and(&nn, &psat, 0, arr, ARRAY_ELEMS(arr));
	sat_and(&nn, &psat, 0, arr, ARRAY_ELEMS(arr));

	sat_nand(&nn, &psat, 0, arr, 1);
	sat_nand(&nn, &psat, 0, arr, ARRAY_ELEMS(arr)  );
	sat_nand(&nn, &psat, 0, arr, ARRAY_ELEMS(arr)-1);

	sat_1ofn(&nn, &psat, 0, arr, 1, 0/*exact 1*/);
	sat_1ofn(&nn, &psat, 0, arr, 2, 0/*exact 1*/);
	sat_1ofn(&nn, &psat, 0, arr, 1, 1/*allow 0/1*/);
	sat_1ofn(&nn, &psat, 0, arr, 2, 1/*allow 0/1*/);

	sat_1ofn(&nn, &psat, 0, arr, 3, 0);
	sat_1ofn(&nn, &psat, 0, arr, 4, 0);

	sat_lt(&nn, &psat, 0, arr, 6, 12);
	sat_lt(&nn, &psat, 0, arr, 6, 25);

	sat_neq_or0(&nn, &psat, 0, arr, 3, &(arr[3]));
	sat_eq(&nn, &psat, 0, arr, 3, &(arr[3]), 0 /* ==? */);

if (0) {
				// XORs are restricted to STC_CLS_MAX_ELEMS
				// build many shorter ones
				//
	for (i=0; i<ARRAY_ELEMS(varr)/STC_CLS_MAX_ELEMS; ++i) {
		for (j=1; j<STC_CLS_MAX_ELEMS; ++j) {
			sat_1ofn(&nn, &psat, 0,
			         &(varr[ STC_CLS_MAX_ELEMS *i ]), j, 0);
		}
	}
}
}
	sat_const(&psat, e0, 0);
	sat_const(&psat, f1, 1);

//	sat_print_clauses(&psat, STC_R_VSTRING | STC_R_EMBED);

	sat_print_clauses(&psat, STC_R_VSTRING | STC_R_VNUMBER | STC_R_EMBED);

//	sat_print_clauses(&psat, STC_R_VNUMBER | STC_R_EMBED);

	sat_print_clauses(&psat, STC_R_VNUMBER | STC_R_EMBED |
	                         STC_R_CLAUSE_ONLY);
	}
	}
	} while (0);

	if (0) {
		rds_hash0(psat.db.rd.ctx, HSH_MAINHASH);
		rds_hash0(psat.db.rd.ctx, HSH_ADDLHASH);
	}
// TODO: control purging

	db_release(&db);
	sat_dispose(&psat);

	return (rc < 0) ? EXIT_FAILURE : EXIT_SUCCESS;
}


#if 0  //=====================================================================
#define  USE_READALL       1
#define  USE_READINT       1
#define  USE_ERR_ANNOTATE  1
#define  USE_ENV_DEFS      /* common-base prerequisite */
//
#include "common-base.h"
#include "common-util.h"

#define  SNHbreak  break   /* marker for should-not-happen errors */

// simplified version of DIMACS solver
//     www.satcompetition.org/2004/format-solvers2004.html
// multiple cross-referencing specs exist; this above is a
// reasonable self-contained summary


// note: ASCII only
// TODO: Unix-only LF (although we use Linux-specific memmem() already)
//
#define  SATSOLV_NO_SOLUTION       "s" "\x20" "UNSATISFIABLE" "\n"
#define  SATSOLV_HAS_SOLUTION      "s" "\x20" "SATISFIABLE"   "\n"
#define  SATSOLV_UNKNOWN_SOLUTION  "s" "\x20" "UNKNOWN"       "\n"
// TODO: we treat this as unsolved
//
#define  SATSOLV_VARLINE_START     "v" "\x20"
//
// these MUST also check if preceding char is either '\n' OR at start
//
#define  SATSOLV_PREFIX_BYTES  ((unsigned int) 2)
// for any of the result-line prefixes


#define  ASCII_LF  '\n'


#define  SATSOLV_INVOCATION0  "kissat"
//
// kissat invocation:
//
static const char *const satsolv_invoc_args[] = {
	"--verbose",
	"--statistics",   // we ignore them now; allow logging at least
	"--sat",          // optimize for solvable case
	NULL,
} ;

typedef void procfn_t (int writefd, int readfd) ;

/* streams to and from another process */
struct ProcComms {
	FILE *tochild;
	FILE *fromchild;
} ;
/**/
#define  PROCCOMMS_INIT0  { NULL, NULL, }

#define  PIPEDIR_READ   0
#define  PIPEDIR_WRITE  1


//--------------------------------------
// reworked equivalent of:
//     stackoverflow.com/questions/3884103/can-popen-make-
//         bidirectional-pipes-like-pipe-fork

/*--------------------------------------
 * create child process, with bidirectional communications to and from it
 * popen() equivalent with simultaneous read+write pipes
 *
 * returns pid >0, filling 'pcomm', for invoking parent
 * calls 'procfn' from child, which does not return
 *
 * TODO: may leak file descriptors if f.ex. one of the fdopen() calls
 * fails, but not all do.
 */
static pid_t procstart(struct ProcComms *pcomm, procfn_t childfn)
{
	int p2child[2], p2parent[2];                     /* read[0] write[0] */
	pid_t parent;

	if (!pcomm)
		return -1;
	*pcomm = (struct ProcComms) PROCCOMMS_INIT0;

	if (pipe(p2child) || pipe(p2parent))
		return -1;

	parent = fork();
	if (parent > 0) {                                          /* parent */
		close(p2child [ PIPEDIR_READ  ]);
		close(p2parent[ PIPEDIR_WRITE ]);

		pcomm->tochild   = fdopen(p2child [ PIPEDIR_WRITE ], "w");
		pcomm->fromchild = fdopen(p2parent[ PIPEDIR_READ  ], "r");

		return (pcomm->tochild && pcomm->fromchild) ? parent : -1 ;

	} else if (!parent) {
		close(p2child [ PIPEDIR_WRITE ]);
		close(p2parent[ PIPEDIR_READ  ]);

		childfn(p2parent[ PIPEDIR_WRITE ], p2child [ PIPEDIR_READ ]);

		exit(0);
	}

	return -1;
}


//--------------------------------------
struct Proc_child {
	pid_t other;

	FILE *tochild;
	FILE *fromchild;
} ;
//
#define PROC_CHILD_INIT0 { 0, NULL, NULL, }


/*--------------------------------------
 * connect a SAT solver which takes DIMACS input and responds
 * with DIMACS solution form
 *
 * instead of worrying about subprocess-related failures, our caller
 * just parses DIMACS results. therefore, opportunistic error handling
 * is sufficient.
 */
static void satsolver1(int writefd, int readfd)
{
	if ((dup2(writefd, STDOUT_FILENO) <0) ||
	    (dup2(readfd,  STDIN_FILENO) <0))
		return;

			// writefd -> (stdin) ...solver... (stdout) -> readfd

	execvp(SATSOLV_INVOCATION0, (char * const *) satsolv_invoc_args);
}


/*--------------------------------------
 * is byte at 'offset' start of a line?
 * start-of-input also interpreted as line start
 *
 * out-of-input reported as not-at-start
 *
 * TODO: restricted to Unix-only lines
 */
static int is_at_line_start(const void *data, size_t dbytes, size_t offset)
{
	const unsigned char *pd = (const unsigned char *) data;

	if (!data || (dbytes <= offset))
		return 0;

	if (!offset)
		return 1;

	if (pd[ offset -1 ] == ASCII_LF)
		return 1;                    // Unix: LF only

// any CR+LF-specific checking etc. would come here

	return 0;
}


/*--------------------------------------
 * retrieve SAT-solver satisfiability response; Boolean only
 *
 * returns >0 if instance is satisfiable
 *         0  if reported unsatisfiable
 *         <0 if any other failure, incl. not finding expected solution type
 */
static int satsolver_result(const void *res, size_t rbytes)
{
	const unsigned char *fnd;

	if (!res || !rbytes)
		return -1;

	fnd = memmem(res, rbytes, SATSOLV_NO_SOLUTION,
	             sizeof(SATSOLV_NO_SOLUTION)-1);
	if (!fnd) {
		fnd = memmem(res, rbytes, SATSOLV_UNKNOWN_SOLUTION,
		             sizeof(SATSOLV_UNKNOWN_SOLUTION)-1);
	}

	if (fnd) {
		return is_at_line_start(res, rbytes,
		                        fnd - (const unsigned char *) res)
		       ? 0 /*known not to be solved*/ : -1 /* TODO: */;

/* TODO: check response w/ filtering out of comment-only lines */
	}

	return memmem(res, rbytes, SATSOLV_HAS_SOLUTION,
	              sizeof(SATSOLV_HAS_SOLUTION)-1)
	       ? 1 : -1 /* not recognized */;
}


//--------------------------------------
#define  SATSOLV_DIMACS_BITMASK    ((uint64_t) -1)  /* bitmask too small */
#define  SATSOLV_DIMACS_INVALID64  ((uint64_t) -2)


/*--------------------------------------
 * only recognized, native-encoded whitespace characters
 */
static size_t whitespace_bytes(const unsigned char *data, size_t dbytes)
{
	if (!data || !dbytes) {
		return 0;

	} else if (data[0] == ' ') {                  // space
		return 1;

	} else if (data[0] == '\t') {                 // tab
		return 1;

	} else if (data[0] == '\n') {                 // (Unix) LF
		return 1;

	} else if ((dbytes > 1) && (data[0] == '\r') && (data[1] == '\n')) {
		return 2;                             // (telnet/Windows) CR+LF

	} else if (data[0] == '\0') {                 // \0, as honorary w.space
		return 1;
	};

	return 0;
}


//--------------------------------------
static inline int is_satsolver_error(uint64_t rc)
{
	switch (rc) {
	case SATSOLV_DIMACS_BITMASK:
	case SATSOLV_DIMACS_INVALID64:
		return 1;

	default:
		return 0;
	}
}


/*--------------------------------------
 * called with one line of variable-index entries, net-net content
 * (DIMACS prefix already removed):
 *     "-643 -644 -645 -646 -647 -648 -649 650 -651 -652 -653"
 *
 * returns maximum 1-based index of variables picked up;
 * SATSOLV_DIMACS_... errors if anything failed
 */
static uint64_t satsolver_register_vars(unsigned char *bits,  size_t bbytes,
                                  const unsigned char *vline, size_t vlbytes)
{
	size_t offs = 0;
	uint64_t rc = 0;

	if (!vline || !vlbytes)
		return 0;

	while (offs < vlbytes) {
		unsigned int is_negative = (vline[ offs ] == '-');
		size_t endoffs;
		uint64_t curr;

		offs += !!is_negative;

		endoffs = offs;

		while ((endoffs < vlbytes) &&
		       !whitespace_bytes(vline +endoffs, 1))
		{
			++endoffs;
		}

		curr = cu_readuint((const char *) vline +offs, endoffs -offs);

		if (curr == CU_INVD_UINT64) {
			rc = SATSOLV_DIMACS_INVALID64;
			break;
		}

		if (!curr)
			break;              // '0' variable terminates var-list
// printf("val=%lu\n", (unsigned long) curr);

		rc = (rc < curr) ? curr : rc;             // max(variable list)

		if (bits && bbytes) {
		}

		offs = endoffs;

		while ((offs < vlbytes) && (vline[ offs ] == ' '))
			++offs;
// DIMACS spec: only space as separator
	}

	return rc;
}


/*--------------------------------------
 * retrieve 0-based bitmask of results from DIMACS response
 * each result bit is 2x wide: <bit seen> || <bit retrieved>
 *
 * returns largest index retrieved
 *         (u64)-1  if result does not fit (non-NULL) bitmask
 *         (u64)-2  if DIMACS output was deemed malformed
 *
 * big-endian bitmask; bits are in the following order: 0x80, 0x40, ... 0x01,
 * 00 0x80, 00 0x40 ...
 * since variable 0 is never used, 0x80 and 0x40 of first bitmask
 * byte are never set
 *
 * tolerates NULL 'bits', just searches for largest index
 *
 * TODO: single-bit response, through 'bbytes' modification, in case
 * we ever worry about gigabit-sized bitmasks
 */
static uint64_t satsolver_result_vars(unsigned char *bits, size_t bbytes,
                                         const void *res,  size_t rbytes)
{
	const unsigned char *pr = (const unsigned char *) res;
	uint64_t rc = 0;
	size_t offs = 0;

	if (!res || !rbytes)
		return 0;

	if (bits && bbytes)
		memset(bits, 0, bbytes);

	while (offs < rbytes) {
		const unsigned char *end, *fnd =
			memmem(pr +offs, rbytes -offs, SATSOLV_VARLINE_START,
			       sizeof(SATSOLV_VARLINE_START) -1);
		uint64_t curr;
		size_t lbytes;

		if (!fnd)
			break;

				// hits in comments, not solution/var-list
		if (fnd && !is_at_line_start(pr, rbytes, fnd -pr)) {
			offs = fnd -pr +1;
			continue;
		}
		offs = fnd - pr;       // [offs] is 1st byte of variables'-line

		offs += SATSOLV_PREFIX_BYTES;         // ...1st net-net byte...

				// either next linefeed byte, or end of
				// input
		end = memchr(pr +offs, ASCII_LF, rbytes -offs);

		if (offs >= rbytes)
			SNHbreak;
				// "v <end-of-file>" is a malformed
				// terminating variable-list line

		lbytes = end ? (end -pr -offs) : (rbytes -offs);

		curr = satsolver_register_vars(bits, bbytes, pr +offs, lbytes);
		if (is_satsolver_error(curr)) {
			rc = curr;
			break;
		}

		rc = (rc < curr) ? curr : rc;        // max(variable list)

		if (!end)
			break;

		offs = end -pr +1;
	}

	return rc;
}


//--------------------------------------
// since SAT solvers work with full input files, 'res' and 'cnf' SHOULD
// work reliably when they are identical.
//
static size_t satsolver_invoke(unsigned char *res, size_t rbytes,
                         const unsigned char *cnf, size_t cbytes)
{
	size_t rc = ~((size_t) 0);

	do {                                  // set rc, break if leaving early
	if (!res || !cnf || !rbytes || !cbytes)
		break;

	{
	struct ProcComms solver;
	size_t offs = 0, curr;

	fflush(stdout);                     // empty streams before sub-process

	if (procstart(&solver, satsolver1) <0)
		break;

	while ((offs < cbytes) && !ferror(solver.tochild)) {
		curr =  fwrite(cnf +offs, 1, cbytes - offs, solver.tochild);
		offs += curr;
	}
	if (ferror(solver.tochild))
		break;

	fclose(solver.tochild);

	offs = 0;

	while ((offs < rbytes) && !ferror(solver.fromchild) &&
	       !feof(solver.fromchild))
	{
		curr =  fread(res +offs, 1, rbytes - offs, solver.fromchild);
		offs += curr;
	}

	if (ferror(solver.fromchild))
		break;

			// opportunistic, possibly redundant 0-termination
	if (offs < rbytes)
		res[ offs ] = '\0';

	rc = offs;
	}
	} while (0);

	return rc;
}
#endif  //====================================================================

