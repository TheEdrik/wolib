#!/usr/bin/python3

## bin-packing/selection: combine elements to maximize utilization
## of fixed-capacity transport.
##
## optionally, observe upper bound on a different ('secondary') value;
## see 'MAX2'  Unlike the primary value, this secondary limit is Boolean.
## Delivery example: optimize for total weight; secondary limit is
## volume of receptacle, assuming perfect packing.
##
## optionally, restrict the number of elements selected ('MAX_ELEMS')
##
## outputs list of not-selected entries if env contains 'NONSEL'


## input format, basic:
##   <primary value>  <secondary value>  <identifier>
##   - no restrictions on repeated primary/secondary/identifier fields
##
## input format, extended:
##   <primary value>  <secondary value>  <X> <Y>  <delivery.times> <identifier>
##   - delivery position X, Y are in arbitrary, but consistent, coord.system
##   - delivery times are HHMM-HHMM start-end tuples, separated with '+'
##     if multi-valued
##     - example: 0915-1015+1100-1130
##     - values need not be sorted or disjunct; start/end sort MUST be proper
##     - TODO: using fixed 15-minute windows currently
##
## internal format
##   <primary value>  <secondary value>  <identifier>  <line number>
##
## env. control
##   MAX1=... selects upper bound on total of primary columns (compulsory)
##   MAX2=...              ---"---            secondary columns
##            optional: secondary columns are ignored if missing
##   MAX_ELEMS=...
##            upper bound on number of elements selected, if specified (>1)
##   FIELD=2  selects secondary column as optimization target
##   PCT=...  stops iterations if solution is no more than 'PCT' of the
##            optimization target MAX1 (floating-point value)
##   NONSEL   set to include full non-selected list after termination
##   DEBUG=...    diagnostics level if >0
##   TUPLE_N=...  limit the size of element-tuples when attempting to swap
##                not-yet-selected and selected elements (see below)
##   TARGET=...host:port...
##            log current-best results as they evolve to socket
##            excluding any other incremental etc. logged data
##            writing results is opportunistic, ignoring sending errors
##   BASE=X,Y[:X,Y...]
##            list of start/refill locations
##
## diagnostics+test
##   RNTIME    randomize time for each delivery
##             if value > 2 characters, it is used as seed
##   RNCOORDS  add randomized, normalized, boundary-delimited random
##             delivery points.  Value of 'RNCOORDS' is boundary file:
##      X Y    ## coordinate pairs, one per line


##----------------------------------------------------------------------------
## optimization target: group records to maximize sum of primary fields
## not above MAX1; total of secondary fields is not above MAX2
##
## - packs bins separately, not attempting multi-bin optimization (i.e.,
##   do not expect group of leftovers to be minimal)
## - we apply best-fit decreasing over primary fields first
##   - generate an initial 'selected set' from BFD-greedy assignment
##     - enumerate candidates in decreasing-sorted primary order
##     - discard candidate which would overload MAX2
##     - select candidate if adding it to the selected set still fits MAX1
##     - no backtracking: only one scan, greedy selection
##   - BFD-generated selection is initial state for further incremental changes
## - iteratively attempt swapping groups of not-selected and selected
##   entries; accept swap if it improves towards MAX1 (and does not
##   violate MAX2); greedy local heuristic
##   - select tuples of 1..MAX_TUPLE_N items each from non/selected lists
##     - with non-negative weights, de-selecting items makes no sense,
##       so only N-to-M swaps with N,M>0 are reasonable
##     - 0-to-M "swaps", just adding to the selection, are possible 
##       - these are simple linear searches, essentially free, do not skip them
##   - references:
##     - Fiduccia, Mattheyses: A Linear-Time Heuristic for Improved Network
##       Partitions, Proceedings DAC, 1982
##     - Kernighan, Lin: An Efficient Heuristic Procedure for Partitioning
##       Electrical Circuits, Bell System Technical Journal, 1970
##       (Fiduccia & Mattheyses reference Kernighan+Lin)
##   - we MAY use special-cased swap code for swapping single items and pairs
##     - straightforward selecting elems from two lists to optimize delta(sum)
## - misc. notes
##   - optional element-count limit restricts possible swaps
##   - equipartition heuristics are _not_ applicable: optimizing for MAX1
##     generally not performed on identical-sized primary and secondary sets
##   - when optimizing for multiple binned entries, repeate procedure for
##     previous non-selected set with identical MAX1 (and MAX2, if applicable)


##=====  nothing user-serviceable below  =====================================
import csv, re, sys, os, operator, functools, itertools, time, json
import socket               ## best-result reporting; ignores all write errors
import random               ## devel only
import pathtools


## keep these global; needs dict if working on context-local limits
##
## MAX2   None  prohibits filtering based on secondary column
## PCT          if non-None, a primary sum which stops iterations
##              when reached (i.e., MAX1 - ...PCT-from-environment...)
## FIELD2 True  implies optimizing for secondary, filtering by primary
##              MUST supply MAX2 in that case
## TUPLE_N      override max-tuples limit
## MAX_ELEMS    >0 if there is an upper limit on number of entries selected
## FORMAT       'json' for REST APIs; default is 'csv'
##
MAX1, MAX2, FIELD2, DEBUG, MAX_ELEMS = None, None, False, 0, 0
TUPLE_N, PCT = 0, None

MAX_TUPLE_N = 4      ## try bundling 1..<this many> entries as single swap unit
                     ## we do not currently build combinations incrementally

tFORMATS = [ 'csv', 'plain', 'json', ]

TARGET = None        ## set to [ host, port ] if env specifies it

CRLF   = b'\n\r'     ## telnet official separator
COMM   = b'#'        ## prefix for commented log results


##--------------------------------------
## 'struct' storing the best solution we have seen so far
## passed around as reference through swap cycle
##
## negative or None sum stands for 'not yet initialized'
##
vSOLUTION = {
	'sum':        -1,
	'selection':  [],
	'nselection': [],
}


##--------------------------------------
def terminate(msg):
	sys.stderr.write(msg +'\n')
	sys.exit(-1)


##--------------------------------------
def usage():
	terminate("""
	Assign
	Usage: <MAX1=...> [MAX2=...] [PCT=...] [DEBUG=...]  ... <input list>
	...usage blurb comes here...
	""")


##--------------------------------------
def debug_is_active(lvl=1):
	return DEBUG and (DEBUG >= 0) and (DEBUG >= lvl)


##--------------------------------------
## returns False to allow set-log-passthrough chains
##
def debugmsg(msg, lvl=1):
	if debug_is_active(lvl):
		print(msg +'\n')
	return False


##--------------------------------------
## returns None if field is not all-numeric[float], suppresses exceptions
##
def str2float(val):
	try:
		return float(val)
	except:
		return None


##--------------------------------------
## returns None if field is not all-numeric[integer], suppresses exceptions
##
def str2num(val):
	try:
		val = int(val)              ## ...float etc. would come here...
		return val
	except:
		return None


##---------------------------------------
## returns 'defval' if key is not present in environment, or is non-numeric
## does not raise exceptions
##
def env2num(key, default=None, expect_float=False):
	n = None
	if key in os.environ:
		n = os.getenv(key)
		n = str2float(n)  if expect_float  else str2num(n)
		if n == None:
			n = default
	return n


##--------------------------------------
def sgn(v1, v2):
	"sign of v1-v2"
	return (v2 < v1) - (v1 < v2)


##--------------------------------------
def socket_open(host, port):
	try:
		s = socket.socket()
		s.connect((host, port))
	except:
		s = None

			## TODO: error reporting

	return s


##--------------------------------------
## report selection to socket
## ignore errors: writing results to remote host is opportunistic
## invoked only if host/port have been supplied (see 'TARGET')
##
## entries of 'prefix' are lines to output commented before input
##
def socketwrite(sock, sel, fmt='csv', prefix=[]):
	"opportunistic write to host/socket"

	if sock and sel:
		hdr = selection2hdr(sel, prefix='#', remain=True)
		sl  = selection2lines(ordered(sel), format=fmt)
		slc = None            ## 'compact' (preformatted) list
		sep = CRLF
		pfx = None

		if prefix:
			pfx =  COMM
			pfx += (sep +COMM).join(l.encode('utf-8')
			                        for l in prefix)

		if fmt == 'json':
			slc = {'selection' : sl}
			slc[ 'total' ] = selection2sum(sel)
			slc[ 'slack' ] = MAX1 - slc[ 'total' ]
			sl  = [ json.dumps(slc, separators=(',', ':')), ]
			hdr, pfx = None, None
			sep = b''

		try:
			if pfx:
				sock.send(pfx +sep)

			if hdr != None:
				sock.send(hdr.encode('utf-8') + sep)

			sock.send(sep.join(s.encode('utf-8') for s in sl))

			if sep == CRLF:
				sock.send(CRLF +CRLF)

			elif fmt == 'json':
				sock.send(CRLF)

		except:
			pass      ## ...should we log?


##--------------------------------------
## works on <primary, secondary, identifier, line nr> tuples
##
## primary/secondary comparisons are reversed, since we descending-order these
##
## TODO: turn into a python3 single-record key() function, move beyond
## this functools.cmp_to_key() workaround
##
def table_cmp(n, m):
	pri, sec = sgn(m[0], n[0]), sgn(m[1], n[1])         ## descending order
	linenr   = sgn(n[3], m[3])

		## value=0 falls to next comparison; line.nr assumed unique
	if pri:
		return pri
	if sec:
		return sec

	return linenr

##--------------------------------------
## given an 'aux' collection of time/time2vec/index dictionaries,
## add any total-collection data:
##   - 'predecessors': [ indexes which always predate this index ]
##   - 'successors':   [ indexes which always appear after this index ]
##
## modifies aux in-place, adding entries
##
def aux2plus(aux):
	pass


##--------------------------------------
## maps HHMM-HHMM[+...] strings to bitvector, with each bit corresponding
## to 'twindow' minutes
##
## vector sets x80 for bit corresponding to 'base..base+twindow', x40
##    for base+twindow..base+twindow*2 etc.
##
## 0915-1015+1100-1130  ->  0000'0111'1000'1100  ->  07'8c
##
## 'twindow' is in minutes
##
## TODO: centralized validate-range etc. checking; these are trivial
## operations in epoch. etc base, HHMM is what complicates things
##
def times2vec(tstr, base=800, twindow=15):
	vec, minv, maxv = 0, 0, 0

	if tstr == '':
		return vec, 0, 0

	units_per_hour = 60 // twindow
	hour2bitmask   = (1 << units_per_hour) -1
	bh             = int(base) // 100            ## base hour

	for w in tstr.split('+'):
		ends = w.split('-')
		if len(ends) != 2:
			raise ValueError(f"invalid time range ({w})")

		s, e = ends
		if (len(s) < 4) or (len(e) < 4):
			raise ValueError(f"malformed time range ({w})")

		if s > e:
			raise ValueError(f"inconsistent time range ({w})")
		if s == e:
			continue

		sh, sm = int(s[:-2]), int(s[-2:])
		eh, em = int(e[:-2]), int(e[-2:])

		if (sh < bh):
			raise ValueError(f"delivery in the past ({w})")

		if (sm > 59) or (em > 59):
			raise ValueError(f"times out of range ({w})")

				## rebase everything to base-hour
		sh -= bh
		eh -= bh

				## units, round to full interval

		su, eu = sm // twindow, (em +twindow -1) // twindow

				## absolute units

		su += sh * units_per_hour
		eu += eh * units_per_hour

		minv = min(su, minv)  if (minv > 0)  else  su
		maxv = max(eu, maxv)

		vec |= (1 << eu) - (1 << su)

	return vec, 1 << minv, 1 << (maxv -1)


##--------------------------------------
## turn "X,Y[:X,Y..." base-list string into array of coordinate pairs
## returns None if input is invalid
##
def str2bases(str):
	b = []

	for xys in str.split(':'):
		x = xys.split(",")
		if len(x) != 2:
			terminate(f"not base coordinates ({xys})")

		try:
			x, y = float(x[0]), float(x[1])
		except ValueError:
			terminate(f"invalid base/coordinate ({xys})")

		b.append([ x, y, ])

	return b


##--------------------------------------
## fetch to list first, since may be called with generators,
## and successful return draws arr twice
##
def arr2sums(arr):
	"return primary+secondary totals of array of entries"
				## tolerates both input and internal forms

	if not arr:
		return 0

	arr = list(arr)

	return sum(e[0] for e in arr), sum(e[1] for e in arr)


##--------------------------------------
def report_env(filehash=None):
	print(f"## MAX1={MAX1}")
	if MAX2:
		print(f"## MAX2={MAX2}")
	if PCT:
		print(f"## PCT={PCT}")

	if filehash:
		print(f"## file.hash={filehash}")
	##
	## TODO: log file date etc.
	print()


##--------------------------------------
## TODO: PPM-formatted reporting chain
##
def ratio(val, maxval=None):
	if maxval == None:
		maxval = MAX1

	if val > maxval:
		return 110.0

	return 100.0 *(maxval - val) /maxval


##--------------------------------------
## 'grp' is internal-format array
## returns its indexes which enumerate group in respective order
##
## file ID is (2); line nr (3) is unique, OK as final tiebreaker
##
def ordered(grp):
	return list(sorted(grp, key=operator.itemgetter(2, 3)))


##--------------------------------------
def elem2str(elem, format='plain'):
	"pretty-format internal-format element (or return empty string)"

	if elem:
		if (format == 'plain'):
			return("id=[{}] pri={} sec={} [line {}]"
			      .format(elem[2], elem[0], elem[1], elem[3]))

		elif (format == 'csv'):
			return(elem[2])

		else:
			raise ValueError("unsupported format")
	return ''


##--------------------------------------
def selection2sum(sel):
	return arr2sums(sel)[0]


##--------------------------------------
def selection2hdr(sel, prefix='', remain=False):
	total = selection2sum(sel)
	r = prefix + f"selection: {len(sel)} elements, total={ total }"

	if remain and (total <= MAX1):
		r += f' margin={ MAX1 - total }/{ MAX1 }'

	return r



##--------------------------------------
def selection2lines(sel, format='plain'):
	"primary,secondary,...element... format [array] of selection"

	if format == 'json':
		res = ([ s[1][0], s[1][1], s[1][2] ]
			for s in list( enumerate(sel) ))

	else:
		res = (f'{s[1][0]},{s[1][1]},{s[1][2]}'
			for s in list( enumerate(sel) ))

	return list(res)



##--------------------------------------
## 'sel' and 'nsel' are internal-format arrays, of current selected
## and non-selected entries, respectively
##
## 'chk_oversize' supported to ensure printing non-selected final
## set, if asked for, is _not_ cross-checked (since it may be larger
## than MAX1)
##
## NOP for empty 
##
def report(sel, nsel, msg=None, remain=True, chk_oversize=True, format='csv'):
	if not format in tFORMATS:
		raise ValueError(f"invalid report format [{format}]")

	stotal, prefix = 0, ''
	if sel:
		stotal = selection2sum(sel)

		if chk_oversize and (stotal > MAX1):
			print("OVERSIZED selection: {} elements, total={}"
			      .format(len(sel), stotal))

			for s in enumerate(ordered(sel)):
				print('OS.elem[{}]: '.format(s[0])
				                     +elem2str(s[1]))
			raise ValueError("ERROR: oversized selection")

	if (msg):
		print(msg)
	if (format == 'csv'):
		prefix = '#'

	print(selection2hdr(sel), end='')
	if remain:
		print(", margin={} ({:.2f}% of {})"
		      .format(MAX1 - stotal, ratio(stotal), MAX1), end='')
	print()

	if sel:
		for s in enumerate(ordered(sel)):
			if (format == 'plain'):
				print('elem[{}]: '.format(s[0])
				      + elem2str(s[1], format))
			else:
				print(f'{s[1][0]},{s[1][1]},' +
				      f'{elem2str(s[1], format)}')
## TODO: shared function -> selection2lines()
		print()

	if nsel:
		if (format == 'csv'):
			print('#', end='')
		print("not selected: {} elements" .format(len(nsel)))

		for s in enumerate(ordered(nsel)):
			print('  ## not.sel[{}]: '.format(s[0]) +elem2str(s[1]))
		print()


##--------------------------------------
## returns array of <primary>, <secondary>, <identifier> tuples, in
## decreasing-primary (then decreasing-secondary) order
##
## skips elements which would not fit if (global) MAX1 and/or MAX2
## are already set; raises exception on clearly invalid data
##
## field '2' swaps primary/secondary columns (compared to file original)
## first two columns MUST be all-numeric; checks for at least three columns
##
## autodetects basic/extended input; returns auxiliary data as:
## [
##   {
##     'time':     '0845-0945+1015-1115',
##     'time2vec': 0x1e78,
##                  --        0001'1110'0111'1000
##                  --             ^ ^  ^  ^  ^ ^
##                  --             | |  |  |  | |
##                  -- 1015-1030 --+ |  |  |  | |
##                  --    ...        |  |  |  | +--  0800-0815
##                  -- 0945-1000 ----+  |  |  |         ...
##                  --    ...           |  |  +----  0830-0845
##                  -- 0915-0930 -------+  |            ...
##                  --                     +-------  0900-0915
##                  --
##                  -- default universal base time is 0800
##
##     'min_time': 0x8,
##     'max_time': 0x1000,
##                  -- LS, MS bit in bitmask
##                  -- used for fast 'X must happen before Y' comparisons
##   }
## ]
##
## TODO: rest of exception handling
##
def table_read(fname, field=1, fmt='base'):
	itype = 'base'
	csvf  = open(fname, newline='')
	rd    = list(csv.reader(csvf, delimiter=',', quotechar='\\'))

	expd_fields = 3

	if (len(rd[0]) < 3) or (len(rd[0]) > 6):
		raise ValueError("pack-job format not recognized")

	if (len(rd[0]) == 6):
		itype = 'extended'
		expd_fields = 6

	res, aux = [], []

	for fi, f in enumerate(rd):
		if len(f) < 3:
			raise ValueError("missing primary/secondary+value " +
			                 f"columns (line { fi+1 })")
		if len(f) != expd_fields:
			raise ValueError(f"unexpected structure (line {fi+1})")

		fd1, fd2 = str2num(f[0]), str2num(f[1])
		if (fd1 == None) or (fd2 == None):
			raise ValueError("non-numeric weight columns")
						## TODO: list up to N errors
		if (field == 2):
			fd1, fd2 = fd2, fd1

		if MAX1 and (fd1 > MAX1):
## TODO: log out-of-band-deliveries
			continue                   ## primary alone > MAX1

		if (MAX2 != None) and (fd2 > MAX2):
## TODO: log out-of-band-deliveries
			continue                   ## secondary alone > MAX2

				## [-1] is element to store, in all
				## current forms
				##
		res.append([fd1, fd2, f[-1], fi+1])

		if (itype == 'extended'):
			t, mint, maxt = times2vec(f[4])
			aux.append({
				'time':     f[4],
				'time2vec': t,
				'index':    fi,
				'min_time': mint,
				'max_time': maxt,
			})

	res = sorted(res, key=functools.cmp_to_key(table_cmp))

	aux2plus(aux)

	return res, aux


##--------------------------------------
## BFD ordering: return two groups, one selected by best-fit-decreasing,
## one containing all rejected records
##
## input has been decreasing-sorted by primary column
##
## 'sum1' and 'sum2' just avoid sum() calls; may replace (expect small N)
## since BFD does not backtrack, these increase-only sums are sufficient
##
## check for early termination with max.elems
## since BFD only looks at largest entries, if we hit the limit here,
## that is our achievable optimum
##
def best_fit_decreasing(tbl, max_elems=0):
	sel, nsel, sum1, sum2, printed = [], [], 0, 0, 0

	for t in tbl:
		ok = True
				## TODO: sanity-check BFD-compatible input
		if len(t) < 4:
			continue

		newsum = sum1 +t[0]
		if newsum > MAX1:
			ok = debugmsg("[primary] out of range", lvl=3)

		if ok and MAX2 and (sum2 +t[1] > MAX2):
			if debug_is_active(2):
				print("## skip secondary " +elem2str(t))
				print("## secondary sum overrun: {}->{}"
				    .format(sum2, sum2 +t[1], MAX1 -sum2 -t[1]))
				printed += 1
			##
			ok = debugmsg("[secondary] out of range", lvl=3)

		if not ok:
			nsel.append(t)
			continue

		if debug_is_active(1):
			print("## add " +elem2str(t))
			print("## sum: {} -> {} [left={}, {:.2f}%]".format(
			      sum1, newsum, MAX1 -newsum, ratio(newsum, MAX1)))
			printed += 1

		sel.append(t)
		if max_elems and (len(sel) >= max_elems):
			debugmsg("terminating BFD after selecting enough "
			         "entries", lvl=2)
			break                ## achievable maximum with N elems

		sum1 += t[0]
		sum2 += t[1]

	if printed:
		print()

	return sel, nsel


##--------------------------------------
## unambiguous string representation of index tuples
## (used to cache sums of )
##
def tuple2idxstring(tuple):
	"itertools....-returned tuple to dict-index-ready string form"
	return "-".join(str(t) for t in tuple)


##--------------------------------------
## update non/selected set: apply add/remove index list
##
## 'prev' and 'curr' >0 implies this change improvement from 'prev' to 'curr'
##
## local copies of arrays are processed: prevent updating [passed-by-ref] arrays
## this is inefficient, but considered tolerably bad for reasonable sizes
##
def add_and_remove(sel, nsel, add_idxs, rm_idxs, curr=0, prev=0, log=True):
	sel, nsel = sel[:], nsel[:]

			## TODO: assert in-range indexes

			## process add/rm indexes in reverse (decreasing)
			## order, so entries are pop'ped back to front
			##
	si  = list(sorted(rm_idxs,  reverse=True))
	nsi = list(sorted(add_idxs, reverse=True))

	if log:
		print("## indexes to deselect: "+ ','.join(str(s) for s in si))
		print("## indexes to select: "+ ','.join(str(s) for s in nsi))
		if curr and prev:
			print(f"## total changes {prev} -> {curr}")

	add = list(nsel.pop(i) for i in nsi)
	rm  = list(sel.pop(i)  for i in si)

	sel.extend(add)
	nsel.extend(rm)

	return sel, nsel


##--------------------------------------
## is there any swap removing 'scount' entries from 'sel' and adding
## 'nscount' from 'nsel' which imporves on primary-sum over current
## selection?
##
## returns: - None, None, None  if no improvement found
##          - array of indexes to move from 'sel' and from 'nsel', plus
##            updated primary sum, respectively, if a selection improves
##            the current selection
##
## 'all_best', when not None, is the global optimum so far, in a 'vSOLUTION'
## styled struct (which is passed by reference)
##
## 'sock', when not None, is an open socket where updates are to be
## written.  These writes are opportunistic, ignoring any exceptions.
##
## since combinations are evaluated in cross-product, cache any sum(...)
## evaluated over non/selected tuples. quality change is difference
## of added/removed tuples (all cached)
##
## caller MUST verify that adding (scount -nscount) to the selection
## still remains under element-count limit
##
def klfm_swap_one(sel, nsel, scount=1, nscount=1, all_best=None, start=None,
                  sock=None):

	if (scount < 1) or (nscount < 1):
		raise ValueError("invalid selection-swap size")

	sum1, sum2 = arr2sums(sel)

	best_sum1, best_sum2, swap_add, swap_del = sum1, sum2, None, None

			## assertion: previous-best sums consistent, <=limit
	if (sum1 > MAX1):
		raise ValueError("invalid swap-initial state (primary)")
	if MAX2 and (sum2 > MAX2):
		raise ValueError("invalid swap-initial state (secondary)")

	if (sum1 == MAX1):
		return None, None, None              ## already primary-optimal

		## return (increasing-ordered) list of entries to swap
		##
	sidx  = list(range(len(sel)))
	nsidx = list(range(len(nsel)))

		## stores [sum(primary), sum(secondary)] for each tuple
		## indexes by '-'-joined string of tuple indexes ("0-1" is
		## tuple [0,1]); non-selected tuples key is prefixed with
		## "n:" ("n:0-1" implies non-selected [0,1])
		##
		## TL/DR: unique index for each non/selected index tuple
	sums = {}

			## TODO: iterator, not enumerating all combinations
			## (instead of explicit loop)

		## brute-force: enumerate sum(primary)+sum(secondary) for each
		## selected N-tuple
		##
		## TODO: trivial simplifications would provide massive speedups
		## we assume non/selected set sizes are not prohibitive
		##
	for st in itertools.combinations(sidx, scount):
		skey = tuple2idxstring(st)
		sums[ skey ] = arr2sums(sel[i] for i in st)

		## same for non-selected items
	for nst in itertools.combinations(nsidx, nscount):
		nskey = "n:" +tuple2idxstring(nst)
		sums[ nskey ] = arr2sums(nsel[i] for i in nst)

				## exhaustive-match potential swap in/out
				## combinations
				##
	for st, nst in itertools.product(
			itertools.combinations(sidx, scount),
			itertools.combinations(nsidx, nscount)):

		skey, nskey = tuple2idxstring(st), "n:" +tuple2idxstring(nst)
		new_best    = None

		assert(skey in sums)              ## MUST have been saved above
		assert(nskey in sums)

				## swapping changes total with:
				## +(sum of non-selected entries just added)
				## -(sum of selected entries just removed)

		if (sums[skey][0] >= sums[nskey][0]):
			continue                ## primary sum does not improve

			## TODO: unchanged primary, improved secondary?

		sum1updated = sum1 -sums[ skey ][0] +sums[ nskey ][0]
		sum2updated = sum2 -sums[ skey ][1] +sums[ nskey ][1]

		if (sum1updated > MAX1):
			continue      ## swap increases primary sum above limit

		if MAX2 and (sum2updated > MAX2):
			continue    ## swap increases secondary sum above limit
	
		if (best_sum1 >= sum1updated):
			continue     ## no improvement over any preceding swaps

				## register this difference as current-best
				##
		best_sum1, best_sum2 = sum1updated, sum2updated
		swap_del, swap_add   = st, nst

		print("## remove:")
		for si in st:
			print('##  - ' +elem2str(sel[si]))

		print("## add:")
		for nsi in nst:
			print('##  + ' +elem2str(nsel[nsi]))

		nbcomment, nbmark = '', ''
		if (all_best != None):
			prevbest = all_best[ 'sum' ]
			if (best_sum1 > prevbest):
				new_best = best_sum1

				debugmsg(f"## global optimum improves "   +
				         f"{all_best['sum']}->{new_best}" +
				         f"(margin: { MAX1 -prevbest }->" +
				         f"{ MAX1 -new_best })")
			else:
				nbcomment = ' (swap is only local optimum)'
				nbmark    = 'L'

				## if this is the global optimum, log it
				## redundant, but it ensures the best choice
				## is somewhere visible in log even during
				## iterations
				##
				## new_best SHOULD be non-None only if all_best
				## is a struct ref, not None
				## please do not comment on this redundancy
				##
		if (new_best != None) and all_best:
			sbest, nsbest = add_and_remove(sel, nsel, swap_add,
			                               swap_del, log=False)

			report(sbest, nsbest, msg='# best combination, so far:')
			all_best[ 'sum'        ] = new_best
			all_best[ 'selection'  ] = sbest
			all_best[ 'nselection' ] = nsbest

			if sock:
				socketwrite(sock, sbest, fmt=fmt)

		tdiff = ''
		if start != None:
			tnow  = time.perf_counter()
			tdiff = f" time(IMPR)={(tnow - start) *1E6:.1f}us "

		print(f"## primary sum improves {sum1}->" +
		      f"{best_sum1}{tdiff}", end='')

		print(f"(remain: { MAX1-sum1 }->{ MAX1-best_sum1 }){nbmark}")
		if nbcomment != '':
			print('##' +nbcomment)
		print(flush=True)


			## possible case: early-terminate: exact match
		if (MAX1 == best_sum1):
			break

	return swap_add, swap_del, best_sum1


##--------------------------------------
def over_pct_threshold(selected):
	if (PCT == None):
		return False

	s = arr2sums(selected)[0]
	if (s >= PCT):
		print(f"## terminating with primary sum ({s}) over " +
		      f"%-threshold ({PCT})")
		return True

	return False


##--------------------------------------
## performs the next reasonable swap, moving entries between non/selected
## groups. selection SHOULD be assumed to be greedy.
##
## updates 'sel' and 'nsel' in-place
##
## returns >0    if selection has been improved: amount of improvement
##         None  if selection is considered optimal under current constraints
##         0     if no improvement, but we MAY improve when called with
##               the same input (such as: timing out in annealing due to
##               resource constraints)
## ...in first parameter; updates and passes back all_best if non-None
##
## 'sel' and 'nsel' are internal-format arrays, of current selected
## and non-selected entries, respectively
##
def klfm_swap(sel, nsel, max_tuple_n, all_best=None, start=None, sock=None):
	if not sel or not nsel:
		return None, None, None

	sum1 = sum(e[0] for e in sel)                            ## start total

			## find best swap possibility from 1..N, 1..N-element
			## combinations from non/selected sets

			## all_best is global optimum
			## best     is for current round of swaps
			##
	best, add, rm = None, None, None

	for scount, nscount in itertools.product(range(1, max_tuple_n +1),
	                                         range(1, max_tuple_n +1)):

		if MAX_ELEMS and ((len(sel) -scount +nscount) > MAX_ELEMS):
			continue                 ## stay below elem-count limit

		s1, s2, nsum = klfm_swap_one(sel, nsel, scount, nscount,
		                             all_best, start=start, sock=sock)

		if (not s1) or (not s2) or (not nsum):
			print('## {}+{} swap: no improvement'
			      .format(scount, nscount))
			continue                       ## no improvement at all

		if best and (nsum <= best):
			continue           ## not better than prev. improvement

		if all_best and (nsum <= all_best[ 'sum' ]):
				## TODO: log improvement but not global
			continue

		best, add, rm = nsum, s1, s2

			## pathological case: terminate: no overhead at all
		if (MAX1 == best):
			break

	if not best:
		return None, None, None                       ## no improvement

	sel, nsel = add_and_remove(sel, nsel, add, rm)

	if all_best != None:
		return all_best -sum1, all_best

	return best -sum1, all_best


##=====  pack-and-route  =====================================================
## passed parsed coordinate+time-equipped delivery plan, and base list
## enumerate possible base-start times and reachable schedules
##
## 'aux' and 'bases' must have been initialized, not empty
##
## iterator: keeps returning improving schedules
##
## creates new plan with [] (default)
## perturbs existing one if passed non-[]
##
def pack_and_route(deliveries, aux, bases, plan=[]):
	sched = []

	if len(deliveries) != len(aux):
		raise ValueError("inconsistent delivery+aux data")
	if not aux:
		raise ValueError("aux.data is uninitialized")

			## time vector: all scheduled delivery windows

	alltime_v = 0
	for d in aux:
		alltime_v |= d[ 'time2vec' ]
## TODO: all-OR (standard aggregator function)

	yield([ 'pack-and-route schedule placeholder' ])


##=====  /pack-and-route  ====================================================


##=====  development only  ===================================================
## weighted set of delivery-window width, single-order windows
tHRS1 = [
	6,
	4, 4, 4, 4,
	3, 3,
	2, 2, 2, 2, 2, 2, 2,
	1, 1,
]
##
## delivery-windows width, 2x orders per day
tHRS2 = [
	2,
	1, 1, 1,
]

vHR_MAX = 18     ## max(schedule delivery), hours HH00
vHR_MIN =  8     ## min(schedule delivery), hours HH00


##--------------------------------------
def duration2start(t):
	## uniform-random selection for 't' (hour) delivery time
	## result is [HH, MM], aligned to 15 minutes
	##
	if (t > vHR_MAX -vHR_MIN):
		raise ValueError("delivery window too wide")

			## 0800 to 2000, quantized to 15 minutes

	if (t == vHR_MAX -vHR_MIN):
		return [ vHR_MIN, 0, ]

	u = (vHR_MAX -vHR_MIN -t) * 4
				## width(available window), in 15-minute units

	v = u
	u = random.randint(0, u)                                 ## actual unit

	return [ vHR_MIN + (u // 4), 15 * (u % 4), ]


##--------------------------------------
## turn 3-field table into 6-field one, adding delivery coordinates
## and randomized time windows
##
## selecting all-day, 1x6, 1x4, 2x1 or 2x2 hour delivery windows
##
## windows are aligned at 15-minute units starting not before 0800,
## ending not after 2000; all-day marked as [0000..2400]
##
## not checking for redundant windows, so 2x2 may end up overlapping
## completely, or partially to form a single 1x3 window
##
def delivery_times():
	"list of [start[H],start[M],end[H],end[M]] tuples as delivery times"
	res = []

	if random.randint(0, 1000) < 3:                             ## full day
		res = [ [0, 2400] ]

	elif random.randint(0, 100) < 50:                ## 1 in 20: two windows
		t   = random.choice(tHRS2)
		s   = duration2start(t)
		res = [ [s[0], s[1]], [s[0] +t, s[1]], ]

	else:
		t1 = random.choice(tHRS2)
		t2 = random.choice(tHRS2)

				## TODO: collapse to minimal, sorted window/s
		s1 = duration2start(t1)
		s2 = duration2start(t2)
				##
		res = [
			[s1[0], s1[1]], [s1[0] +t1, s1[1]],
			[s2[0], s2[1]], [s2[0] +t2, s2[1]],
		]

	return res


##--------------------------------------
def xy2print(x, y):
	return f'{x:.08f}', f'{y:.08f}'


##--------------------------------------
## TODO: split out perturbation code, then replace with list operation
##
def times2print(t):
	"human-readable form of start+end time tuple"

	res = []
	for i in range(len(t) // 2):
					## pair of (H, M) tuples
		s, e = t[i+i], t[i+i+1]

					## any perturbation etc.
					## would be added here

		res.append(f'{s[0]:02}{s[1]:02}-{e[0]:02}{e[1]:02}')

	return "+".join(res)


##--------------------------------------
## call only with RNTIME set
## adds random, in-polygon points if 'RNCOORDS' is set
##
## TODO: centralized polygon reading, pass through 'border',
##       do not read RNCOORDS directly
##
def table_partial2full(t, border=None):
	if 'RNTIME' in os.environ:
		seed = os.environ[ 'RNTIME' ]
		if len(seed) >= 2:
			random.seed( seed.encode('utf-8') )

	deliveries = list(delivery_times() for _ in t)
	coords = []

	if 'RNCOORDS' in os.environ:
		border = (t.decode().split() for t in
		         open(os.environ['RNCOORDS'], 'rb').read().split(b'\n'))
			##
		border = list([float(t[0]), float(t[1])]
		              for t in border  if (len(t) == 2))
			##
			## X+Y segments, preserving order

		brd, prevx, prevy = [], border[0][0], border[0][1]
		for x,y in border[1:]:
			brd.append([
				prevx, prevy, x, y,
				min(x, prevx),
				max(x, prevx),
				min(y, prevy),
				max(y, prevy),
			])
			prevx, prevy = x, y
		border = brd


			## generate delivery points, within polygon
		while len(coords) < len(t):
			x = random.randint(0, 1<<64)
			y = random.randint(0, 1<<64)
			x /= (1 << 64)
			y /= (1 << 64)

			if not pathtools.is_inside(x, y, border):
				continue

			coords.append([x, y])


			## 1-based indexes may have skipped empty lines etc.
			## len(t) may not be sufficient
			##
	res = max(v[-1]  for v in t)                     ## max. index, 1-based
	res = list([]  for _ in range(res +1))
			##
			## special case: [0] * 2  is [0, 0]
			##               []  * 2  is []; needs range+list

			## in: [primary, secondary, item, index]
			## [9267620, 1, 'from-russia-with-love83.mkv', 3] 
			##
	for v, d, xy in zip(t, deliveries, coords):
		idx = v[ -1 ]
		pd  = times2print(d)
		xy  = xy2print(xy[0], xy[1])
		res[ idx ].extend([ v[0], v[1], xy[0], xy[1], pd, v[2], ])

	for r in (r  for r in res  if (r != [])):
		print(','.join(str(v) for v in r))

	return 0


##=====  /development only  ==================================================


##--------------------------------------
if __name__ == '__main__':
##---  TODO: factor out: parameter-read code
	if 'FIELD' in os.environ:
		if os.getenv('FIELD') == '2':
			FIELD2 = True
		elif os.getenv('FIELD') != '1':
			terminate('unsupported FIELD value [{}]'
			          .format(os.getenv('FIELD')))

	sock, fmt = None, 'csv'
	if 'TARGET' in os.environ:
		t = os.getenv('TARGET')
				## TODO: prepackaged env2num()-like macro
		if ':' in t:
			t = t.split(':')
			try:
				t[1] = int(t[1])
			except:
				t = []
		else:
			t = [ 'fail below' ]
		if len(t) < 2:
			terminate('missing or invalid TARGET host/port')
		elif len(t) > 2:
			terminate('malformed TARGET host/port specification')

				## TODO: proper report

		sock = socket_open(t[0], t[1])
## TODO: wrap with proper exceptions to wrapper


	n = env2num('TUPLE_N')
	if (n != None):
		if (n < 1):
			raise ValueError("tuple size out of range ({})"
			                 .format(TUPLE_N))
		MAX_TUPLE_N = n

	DEBUG = env2num('DEBUG', 0)

	if not 'MAX1' in os.environ:
		terminate("need MAX1 [optimization-target] definition")

	MAX1 = str2num(os.getenv('MAX1'))
	if (MAX1 == None) or (MAX1 <= 0):
		terminate(f"invalid MAX1 definition [{MAX1}]")
	if (MAX1 <= 0):
		terminate(f"MAX1 def out of range [{MAX1}]")

	MAX2 = env2num('MAX2', 0)     ## MAX2 is optional; default None is fine
	if (MAX2 == None) and ('MAX2' in os.environ):
		terminate(f"invalid MAX2 definition [{os.getenv('MAX2')}]")
	elif MAX2 and (MAX2 < 0):
		terminate(f"MAX2 value out of range [{MAX2}]")
	elif (MAX2 == 0):
		MAX2 = None

	PCT = env2num('PCT', None, expect_float=True)
	if (PCT == None) and ('PCT' in os.environ):
		terminate(f"invalid PCT definition [{os.getenv('PCT')}]")
	elif (PCT and ((PCT < 0) or (PCT >= 100))):
		terminate(f"PCT value out of range [{PCT}]")
	elif (PCT == 0):
		PCT = None

	if PCT != None:
		PCT = int((float(MAX1) * (100 - PCT)) / 100.0)

	if ('FORMAT' in os.environ):
		fmt = os.environ[ 'FORMAT' ]
		if not fmt in tFORMATS:
			terminate(f"unknown format ({fmt})")

	MAX_ELEMS = env2num('MAX_ELEMS', 0)      ## optional; default 0 is fine
	if (MAX_ELEMS == None) and ('MAX_ELEMS' in os.environ):
		terminate("invalid MAX_ELEMS definition [{}]"
		          .format(os.getenv('MAX_ELEMS')))

	elif MAX_ELEMS and (MAX_ELEMS < 0):
		terminate("MAX_ELEMS def out of range [{}]".format(MAX_ELEMS))

	bases = None
	if ('BASE' in os.environ):
		bases = str2bases(os.environ[ 'BASE' ])
		if not bases:
			terminate("invalid list of bases (" +
			          f"{ os.environ[ 'BASE' ] })")
##---  /parameter-read code

	sys.argv.pop(0)
	if [] == sys.argv:
		usage()
	tbl, aux = table_read(sys.argv[0], 2  if FIELD2  else 1, fmt='base')

	if 'RNTIME' in os.environ:
		sys.exit( table_partial2full(tbl) )

	if bases and aux:
		for sched in pack_and_route(tbl, aux, bases):
			print('TODO: schedule placeholder', sched)
		sys.exit(0)

	tstart = time.perf_counter()

	report_env()
	sel, nsel = best_fit_decreasing(tbl, MAX_ELEMS)

	tend   = time.perf_counter()
	print(f"## time(BFD)={ (tend - tstart) *1E6 :.2f}us")
	tstrt  = tend

	report(sel, nsel, msg='best-fit decreasing raw output:')
	if sock:
		socketwrite(sock, sel, fmt=fmt, prefix=['BFD.plan'])

	impr, round = True, 0
	vSOLUTION[ 'sum'        ] = arr2sums(sel)[0]
	vSOLUTION[ 'selection'  ] = []
	vSOLUTION[ 'nselection' ] = []
		## these will be filled if any swap improves on BFD plan

	while impr:
		if over_pct_threshold(sel):
			break

		plus, minus, impr = klfm_swap(sel, nsel, MAX_TUPLE_N,
		                         vSOLUTION, start=tstart, sock=sock)
		round += 1

		if impr and (impr > 0):
			report(sel, nsel, msg=f'KLFM improvement, r {round}')
			if over_pct_threshold(sel):
				break

	sel, nsel = vSOLUTION[ 'selection' ], vSOLUTION[ 'nselection' ]

	print()
	report(sel, None, msg=f'final packing proposal ({MAX_TUPLE_N}' +
	                      f'+{MAX_TUPLE_N} tuples):')

	if 'NONSEL' in os.environ:
		if nsel:
			report(nsel, None, msg='non-selected items:',
			       remain=False, chk_oversize=False)

