/*------------------------------------------------------------------------
 * minimal in-memory hash table for moderate amounts of data.
 *------------------------------------------------------------------------
 *  Author: Tamas Visegrady  <tamas@visegrady.ch>
 *----------------------------------------------------------------------*/

/* in-memory hash and backing string, with finite capacity.
 *
 * check imhstr_main and imhash_main: they are available to the
 * including application.  imhstr_main contains concatenated content
 * as it is added to the hash table; imhash_main provides an index.
 *
 * only imhstr_main may be reallocated during regular use. we only
 * store offsets and lengths in our tables, therefore reallocation
 * is always safe.
 *
 * public functions
 *   size_t imh_append(size_t *offs, uint32_t *idx,
 *                 const void *data,   size_t dbytes) ;
 *           -- register (data, dbytes) as new content
 *           -- returns stored bytecount +1 upon success
 *           --         IMH_SIZE_INVALID    if anything failed, which is
 *           --                             above any reasonable size
 *           -- returns newly added index >0 with non-NULL 'idx'
 *           -- returns offset into imhstr_main with non-NULL 'offs'
 *
 *   uint32_t imh_idx(const void *data, size_t dbytes) ;
 *           -- returns 1-based index >0 [into imhash_main] if found
 *           --         0  if (data, dbytes) is not found in table
 *
 *   const void *imh_entry(size_t *dbytes, uint32_t idx) ;
 *           -- returns pointer+bytecount to current position of 1-based 'idx'
 *           -- added to use chained-through imh_idx() result
 *           --
 *           -- note: since table is inlined into caller's code+memory,
 *           -- we do not worry about providing direct (read-only) access.
 *
 *   void imh_main_dispose(void) ;
 *           -- release any memory allocations; in-memory structures'
 *           -- contents are not available subsequently.
 *
 * functions are static unless USE_NO_STATIC is defined.
 *
 * we intend this code to be inlined into an application, generally in
 * VMs, not shared. therefore, we define structs, but expect to use only
 * a single, global instance. our application around the library
 * code is single-user, non-reentrant: it works on inherently
 * serialized operations.
 *
 * please do not comment on these choices.
 */


/* configuration during include time:
 *
 * table is structured as 2^IMH_IDX_BITS slots of IMH_SLOT_ENTRIES each
 * we do not cross-check user-supplied values
 *
 * initial allocation for aux. data IMH_ALLOC1_BYTES; subsequent
 * extensions are in units of IMH_EXTEND_BYTES. we provide
 * reasonable defaults (we believe).
 */

#if !defined(IMH_IDX_BITS)
#define  IMH_IDX_BITS      ((unsigned int) 20)                  // 2^IDX slots
#endif
/**/
#if !defined(IMH_SLOT_ENTRIES)
#define  IMH_SLOT_ENTRIES  ((unsigned int) 16)                  // per slot
					// suitable for 64-byte cache lines
#endif

//-----  nothing user-serviceable below  -------------------------------------

#if !defined(IMH_HASH__)  //-----  delimiter: hash approximation  ------------
#define IMH_HASH__ 1

#include <stdlib.h>
#include <stdint.h>

#define  USE_SIPHASH_S
#define  USE_HEXDUMP   -1
#include "common-util.h"


#if defined(USE_NO_STATIC)
#define IMH__STATIC /**/
#else
#define IMH__STATIC static
#endif

#define  IMH_SIZE_INVALID   (~((size_t) 0))
#define  IMH__UINT_INVALID  (~((unsigned int) 0))


// allocation includes entry-separating \0's
//
static struct IMHString {
	unsigned char *ps;
	size_t allocd;
	size_t used;
} imhstr_main ;
//
#if !defined(IMH_ALLOC1_BYTES)
#define  IMH_ALLOC1_BYTES  ((size_t) 100000000)
#endif
//
#if !defined(IMH_EXTEND_BYTES)
#define  IMH_EXTEND_BYTES  ((size_t) 4000000)
#endif


//--------------------------------------
#define  IMH_ELEMENTS      ((1 << IMH_IDX_BITS) * IMH_SLOT_ENTRIES)
//
struct IMHSlot {
	uint32_t offs;
	uint32_t fullhash;
	uint32_t bytes;            // short IDs->lengths only
	                           // note expected u16->u32 pad
} ;
// stores (offset, bytecount) into a separately allocated memory region
// (0, 0) means unused
//
// struct not expected to be stack-allocated
struct IMHash {
	struct IMHSlot entries[ IMH_ELEMENTS ];
				// offset, length into imhstr_main above
				// first (0, 0) offset+bytecount terminates
	unsigned int used;

// TODO: replicate fullhash, so searching idx[] alone can
// compare hash

	uint32_t idx[ 1 << IMH_IDX_BITS ][ IMH_SLOT_ENTRIES ];
				// 1-based index into offs[] and bytes[]
				// first 0 entry within [] terminates
				// 16 per 64-byte cache line
				//
				// use imh__hash2slot() to map
				// uint32_t hash to slot selection

	unsigned int maxentries;  // in any of the slots

	unsigned char hkey[ 128/8 ];                             // siphash key
} imhash_main ;


#if 1   //-----  delimiter: SipHash  -----------------------------------------
#define RL32(x, n) ((((uint32_t) (x)) << (n)) | (((uint32_t) (x)) >> (32-(n))))

#define SIPH__HF_ROUND(v0, v1, v2, v3)   \
	do {                             \
		(v0) += (v1);            \
		(v1) =  RL32((v1), 5);   \
		(v1) ^= (v0);            \
		(v0) =  RL32((v0), 16);  \
		(v2) += (v3);            \
		(v3) =  RL32((v3), 8);   \
		(v3) ^= (v2);            \
		(v0) += (v3);            \
		(v3) =  RL32((v3), 7);   \
		(v3) ^= (v0);            \
		(v2) += (v1);            \
		(v1) =  RL32((v1), 13);  \
		(v1) ^= (v2);            \
		(v2) =  RL32((v2), 16);  \
	} while (0)


/*--------------------------------------
 */
static INLINE
uint32_t cu_siphash_s(const unsigned char *data, size_t dbytes,
                      const unsigned char *key)
{
	const unsigned char *end = data ? (data +dbytes -(dbytes %4)) : NULL;
	uint32_t v0 = 0,
	         v1 = 0,
	         v2 = UINT32_C(0x6c796765),
	         v3 = UINT32_C(0x74656462);
	uint32_t k0 = key ? LSBF4_READ(key)    : 0;
	uint32_t k1 = key ? LSBF4_READ(key +4) : 0;
	uint32_t b  = data ? (((uint32_t) dbytes) << 24) : 0;

	v3 ^= k1;
	v2 ^= k0;
	v1  = k1;    // was 0-initialized
	v0  = k0;

	while (data != end) {
		uint32_t m = LSBF4_READ(data);

		v3 ^= m;
		SIPH__HF_ROUND(v0, v1, v2, v3);
		SIPH__HF_ROUND(v0, v1, v2, v3);
		v0 ^= m;

		data += 32/8;
	}

	switch (data ? (dbytes % 4) : 0) {
	case 3:
		b |= (LSBF2_READ(data +1) << 8) | data[0];
		break;
	case 2:
		b |= LSBF2_READ(data);
		break;
	case 1:
		b |= data[0];
		break;
	case 0:
		break;
	}

	v3 ^= b;
	SIPH__HF_ROUND(v0, v1, v2, v3);          /* 2 from ...-2-4 */
	SIPH__HF_ROUND(v0, v1, v2, v3);

	v0 ^= b;
	v2 ^= 0xff;
	SIPH__HF_ROUND(v0, v1, v2, v3);          /* 4 from ...-2-4 */
	SIPH__HF_ROUND(v0, v1, v2, v3);
	SIPH__HF_ROUND(v0, v1, v2, v3);
	SIPH__HF_ROUND(v0, v1, v2, v3);

	return v1 ^ v3;
}

#endif   //-----  /delimiter: SipHash  ---------------------------------------


//--------------------------------------
static uint32_t imh__data2hash(const unsigned char *data, size_t dbytes)
{
	return (uint32_t) cu_siphash_s(data, dbytes, imhash_main.hkey);
}


//--------------------------------------
IMH__STATIC void imh_main_dispose(void)
{
	free(imhstr_main.ps);

	memset(&imhstr_main, 0, sizeof(imhstr_main));
}


//--------------------------------------
static inline unsigned int imh__hash2slot(uint32_t hash)
{
	return hash & ((((uint32_t) 1) << IMH_IDX_BITS) -1);
}


/*--------------------------------------
 * hash indexing takes the LS IMH_IDX_BITS of a u32 to select slot,
 * then scan all entries there.
 *
 * index within hash slot
 * IMH__UINT_INVALID  if all entries are occupied, or table is inconsistent
 */
static unsigned int imh__add_hash2slotidx(uint32_t hash)
{
	unsigned int i, slot = imh__hash2slot(hash);

	for (i=0; i<IMH_SLOT_ENTRIES; ++i) {
		if (!imhash_main.idx[ slot ][ i ])
			return i;
	}

	return IMH__UINT_INVALID;
}


/*--------------------------------------
 * hash table full, or inconsistent
 * 'slotidx' has been returned by imh__add_hash2slotidx() search
 *
 * all the consistency etc. failures are considered 'should-not-happen'
 */
static inline int hash_is_out_of_mem(unsigned int slotidx)
{
	if (slotidx == ~((unsigned int) 0))
		return 1;                               // slot full

	if (imhash_main.used > IMH_ELEMENTS)
		return 2;                               // invalid state struct

	if (imhash_main.used == IMH_ELEMENTS)
		return 3;                               // table just filled up

	if (imhstr_main.used > imhstr_main.allocd)
		return 4;                               // state inconsistent

	return 0;
}


//--------------------------------------
// registers new entry to imhstr_main, and to index imhash_main
// returns IMH_SIZE_INVALID if running out of memory, or index
//
// 'offs' and 'idx' store the offset of first written byte (imhstr_main)
// and 1-based index of newly allocated entry (imhash_main), if non-NULL
//
// TODO: report index errors differently (although in practical
// settings we do not reindex, just terminate)
//
IMH__STATIC
size_t imh_append(size_t *offs, uint32_t *idx, const void *data, size_t dbytes)
{
	size_t rc = 0;

	do {
	if (data && dbytes) {
		const unsigned char *pd = (const unsigned char *) data;
		unsigned int hidx = imhash_main.used;
		uint32_t hash32   = imh__data2hash(pd, dbytes);
		unsigned int next = imh__add_hash2slotidx(hash32);

		if (hash_is_out_of_mem(next)) {
			rc = IMH_SIZE_INVALID;
			break;
		}

		if (!imhstr_main.ps) {
			imhstr_main.ps = calloc(IMH_ALLOC1_BYTES, 1);

			if (imhstr_main.ps) {
				imhstr_main.used   = 0;
				imhstr_main.allocd = dbytes +1;
				rc = dbytes;
			} else {
				rc = IMH_SIZE_INVALID;
				break;
			}

		} else if (imhstr_main.used +dbytes +1 > imhstr_main.allocd) {
			size_t nbytes = imhstr_main.used +IMH_EXTEND_BYTES +1;
			void *pn      = realloc(imhstr_main.ps, nbytes);

			if (pn) {
				imhstr_main.ps     = pn;
				imhstr_main.allocd = nbytes;
			} else {
				rc = IMH_SIZE_INVALID;
				break;
			}
		}                      // else: .ps already present, still fits

		//-----  update hash indexes  --------------------------------

		if (idx)
			*idx = hidx +1;

		imhash_main.idx[ imh__hash2slot(hash32) ][ next ] = hidx+1;

		if (imhash_main.maxentries < next +1)
			imhash_main.maxentries = next +1;

		imhash_main.entries[ hidx ].offs     = imhstr_main.used;
		imhash_main.entries[ hidx ].bytes    = dbytes;
		imhash_main.entries[ hidx ].fullhash = hash32;
		imhash_main.used++;

		//-----  update merged string  -------------------------------

		memcpy(&(imhstr_main.ps[ imhstr_main.used ]), pd, dbytes);

		if (offs)
			*offs = imhstr_main.used;

		imhstr_main.used += dbytes +1;

		imhstr_main.ps[ imhstr_main.used -1 ] = '\0';    // 0-terminate

		rc = dbytes +1;
	}
	} while (0);

	return rc;
}


/*--------------------------------------
 * 'idx' is 1-based
 * returned pointer is valid only until next update
 */
IMH__STATIC
const void *imh_entry(size_t *dbytes, uint32_t idx)
{
	const unsigned char *base = imhstr_main.ps;

	if (dbytes)
		*dbytes = 0;

	if (!base || !idx || (idx > IMH_ELEMENTS))
		return NULL;

	if (!imhash_main.entries[ idx -1 ].bytes)
		return NULL;

// TODO: factor out as inconsistent state+idx check
	{
	if (imhstr_main.used > imhstr_main.allocd)
		return NULL;                     // TABLE IN INCONSISTENT STATE

	if ((imhash_main.entries[ idx -1 ].offs +
	     imhash_main.entries[ idx -1 ].bytes) > imhstr_main.used)
	{
		return NULL;                     // TABLE IN INCONSISTENT STATE
	}
	}

	if (dbytes)
		*dbytes = imhash_main.entries[ idx -1 ].bytes;

	return base + imhash_main.entries[ idx -1 ].offs;
}


/*--------------------------------------
 * do not expect to hash-index an empty string
 */
IMH__STATIC
uint32_t imh_idx(const void *data, size_t dbytes)
{
	uint32_t hash32 = imh__data2hash(data, dbytes);
	unsigned int i, slot = imh__hash2slot(hash32);

	if (!data || !dbytes || !imhstr_main.ps || (dbytes > imhstr_main.used))
		return 0;                    // incl. not enough stored string

	for (i=0; i<IMH_SLOT_ENTRIES; ++i) {
		uint32_t entry = imhash_main.idx[ slot ][ i ];
		size_t offs, bytes;

		if (!entry)
			return 0;            // no more hash entries, not found

		if (entry > IMH_ELEMENTS)
			return 0;            // NOTE: INVALID HASH STATE

		if (imhash_main.entries[ entry -1 ].fullhash != hash32)
			continue;            // hash(input) != hash(from table)

		bytes = imhash_main.entries[ entry -1 ].bytes;
		offs  = imhash_main.entries[ entry -1 ].offs;

		if (bytes != dbytes)
			continue;

		if ((offs > imhstr_main.used) ||
		    (offs +bytes > imhstr_main.used))
			return 0;            // NOTE: INVALID HASH+STRING STATE

		if (!memcmp(&(imhstr_main.ps[ offs ]), data, bytes))
			return entry;
	}

	return 0;
}
#endif //-----  !IMH_HASH__  -------------------------------------------------

