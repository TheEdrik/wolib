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

#undef   SYS_NO_LMDB
#define  SYS_NO_LMDB  1  /* workaround: needs rest of transaction/logic */

#include <hiredis/hiredis.h>
#include <hiredis/read.h>

#define  USE_READINT
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

#define STC_ADDL_UNITS  ((unsigned int) 10000)  /* grow arrays in such units */
#define STC_STR_UNITS   ((size_t) 1000000)    /* collated string growth size */


#define STC_REP_PREFIX         "SAT="
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
	uint32_t soffset[ STC_VEC_SIGN_U64S *64 ];
	unsigned char sbytes[ STC_VEC_SIGN_U64S *64 ];

// TODO: once we increase length limit, it is prob. simpler to just store
// arrays of compact strings

	uint64_t comment;

	unsigned int used;
} ;
//
#define SAT_CLAUSE0  { {0,}, {0,}, {0,}, 0, 0, }


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


struct SatStrings {
	unsigned char *strs;
	size_t used;              // offset of first available byte
	size_t allocd;

// TODO: offset and size arrays
} ;
//
#define SAT_STRINGS0  { NULL, 0, 0, }


//--------------------------------------
struct SatState {
	struct PNR_DB db;

	struct SatStrings s;

	struct SatStrings comments;

	struct SatClause *c;
	unsigned int c_used;          // nr. of clauses already populated
	unsigned int c_allocd;

	unsigned int vars;          // total nr. of variables added
	unsigned int addvars;       // number of additional, indirect etc.
	                            // variables
	unsigned int nzclauses;     // non-comment, non-empty clauses
} ;


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
 * at least 'n' clauses are available in 'ps'
 */
static int sat_ensure_clauses(struct SatState *ps, unsigned int n)
{
	if (ps && n) {
// TODO: centralized check for .used <= .allocd etc

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
				return -1;
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
 * valid-looking allocated/used limts?
 */
static inline int has_valid_strings(const struct SatState *ps)
{
	if (!ps || !ps->s.strs)
		return 0;

	return (ps->s.used <= ps->s.allocd);
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


#if 1    /*-----  delimiter: SAT/CNF-construction primitives  --------------*/
/* register +incr clauses (all functional)
 */
static inline void sat_register_clauses(struct SatState *ps, unsigned int incr)
{
	if (ps && incr) {
		ps->c_used    += incr;
		ps->nzclauses += incr;
	}
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
                                      int invert) ;


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

		sat_or(&discard, ps, 0, a, an - runs.total, 1/*NOR*/);
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
                                      int invert)
{
	uint64_t xors[ STC_CLS_MAX_ELEMS ] = { 0, };
	char descr[ STC_STR_MAX_BYTES +1 ];
	struct SatName eq = SAT_NAME_INIT0;
	unsigned int idx0, i;
	size_t cb;

	if (!ps || !a || !an || (an > STC_CLS_MAX_ELEMS) || !b)
		return 0;

	idx0 = sat_state2clausecnt(ps);

	cb = snprintf(descr, sizeof(descr), "%s" "EQ(%u)",
	              invert ? "NOT-" : "", an);
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

	if (!sat_or(name, ps, r, xors, an, !invert))
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

	if (!sat_or(&nor1, ps, 0, a, an, 1 /* NOR */) ||
	    !sat_or(&nor2, ps, 0, b, an, 1 /* NOR */) ||
	    !sat_eq(&eq,   ps, 0, a, an, b, 1 /* != */))
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
static unsigned int
valid_np1_params(const struct SatName *name,
                const struct SatState *ps,
                             uint64_t r,
                       const uint64_t *a, unsigned int an)
{
	unsigned int i;

	if (!ps || !a || (!name && !r))
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
 * 'invert' flips sign of R, turns OR into NOR
 */
static unsigned int sat_or(struct SatName *name,
                          struct SatState *ps,
                                 uint64_t r,
                           const uint64_t *a, unsigned int an,
                                      int invert)
{
	char descr[ STC_STR_MAX_BYTES +1 ];
	struct SatClause *pc;
	unsigned int idx, i;
	size_t cb;

	if (!valid_np1_params(name, ps, r, a, an))
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

		if (invert) {
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
	              invert ? "N" : "", an);
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
	pc[ idx ].neg[ 0 ] = ((uint64_t) !invert) << (63 - an);
						// NOT(R) (=OR) or R (=NOR)


	for (i=0; i<an; ++i) {
		pc[ idx +1 +i ].soffset[ 0 ] = cstring2offset(a[ i ]);
		pc[ idx +1 +i ].sbytes [ 0 ] =  cstring2bytes(a[ i ]);
		pc[ idx +1 +i ].soffset[ 1 ] = cstring2offset(r);
		pc[ idx +1 +i ].sbytes [ 1 ] =  cstring2bytes(r);
						// NOT(A) | R ... NOT(H) | R

		pc[ idx +1 +i ].neg[ 0 ] = ((uint64_t) (2 | !!invert)) << 62;
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
 * 'verbose' is bitmask, see SatReport_t for bits
 *
 * note: DB access may need to update context etc. in 'ps', so not constant
 */
static int sat_print_clauses(struct SatState *ps, uint32_t mode)
{
	const struct SatClause *pc = ps ? ps-> c : NULL;
	struct SatFormat fmt = SAT_FORMAT0;
	unsigned int c, v, nzclauses = 0;

	if (!has_valid_strings(ps) || !has_valid_clauses(ps) ||
	    !has_valid_comments(ps))
		return 0;

	if (!(STC_R_NOFRAME & mode)) {
		if (STC_R_EMBED & mode)
			printf("%s", STC_REP_PREFIX);

		printf("p cnf %u %u\n", ps->vars +ps->addvars, ps->nzclauses);
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
static void sat_dispose(struct SatState *ps)
{
	if (ps) {
		free(ps->comments.strs);
		free(ps->s.strs);
		free(ps->c);

		memset(ps, 0, sizeof(*ps));
	}
}

#endif   /*=====  !delimiter: SAT converter  ===============================*/


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

	for (i=0; i<ARRAY_ELEMS(varr); ++i) {
		size_t wr;

		wr = snprintf(tmpname, sizeof(tmpname), "d999t%04u", i);

		varr[i] = sat_name2cs(&psat, tmpname, wr, HSH_MAINHASH);
		if (!varr[i])
			return -1;
	}
	}

	{
	uint64_t arr[6] = { a, b, c, d, e0, f1 };
	struct SatName nn;

	sat_xor1(&nn, &psat, 0, c, d, 0);
	sat_xor1(&nn, &psat, 0, a, c, 1);

	sat_or(NULL, &psat, r, arr, ARRAY_ELEMS(arr), 0);
	sat_or(NULL, &psat, r, arr, ARRAY_ELEMS(arr), 1/*NOR*/);
	sat_or(&nn, &psat, 0, arr, ARRAY_ELEMS(arr), 0);
	sat_or(&nn, &psat, 0, arr, ARRAY_ELEMS(arr), 1/*NOR*/);

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

	db_release(&db);
	sat_dispose(&psat);

	return (rc < 0) ? EXIT_FAILURE : EXIT_SUCCESS;
}

