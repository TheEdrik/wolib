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
## runtime form is extended with 1-based input index (position in
## original input)
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
##   TRACE=...    comma-separated list of features to trace, regardless
##                of diagnostics level (DEBUG):
##                time   execution time
##   TUPLE_N=...  limit the size of element-tuples when attempting to swap
##                not-yet-selected and selected elements (see below)
##   TARGET=...host:port...
##            log current-best results as they evolve to socket
##            excluding any other incremental etc. logged data
##            writing results is opportunistic, ignoring sending errors
##   BASES=X,Y[:X,Y...]
##            list of start/refill locations
##            alt. BASE=...file containing X,Y pairs of bases...
##   VREFILL=[V.ID1]=[...time spec...][:V.ID2=[...time spec...]...]
##            vehicle refills.  Vehicle ID1 must be refilled in given time
##            window/s; Vehicle ID2 in other windows etc.
##            Multiple windows MAY repeat for the same vehicle; these imply
##            different refill windows; example with two distinct refills:
##              V.ID1=1200-1300,1400-1500  1st shift ends 1200-1300 OR 1400-1500
##              V.ID1=1600-1730            2nd shift ends 1600-1730
##            These are different program points, each possibly with multiple
##            feasible completion windows.
##            Vehicle IDs MUST be all-numeric.
##   DIST=...filename of XY-to-distance JSON table...
##            simple distance-based approximation used if not supplied
##
## auxiliary functionality
##   XY2TABLE  generate point-to-point time/cost lookup table
##             requires extended input format
##             outputs JSON table, with X/Y indexing costs as strings
##   TO_C      generate result for direct inclusion into C source
##             TODO: external spec for including C
##
## diagnostics+test
##   SEED0     use common seed for randomized operations
##             MAY NOT BE PORTABLE ACROSS PYTHON VERSIONS
##   RNTIME    randomize time for each delivery
##             if value > 2 characters, it is used as seed if SEED0 not set
##   RNCOORDS  add randomized, normalized, boundary-delimited random
##             delivery points.  Value of 'RNCOORDS' is boundary file:
##      X Y    ## coordinate pairs, one per line, in boundary order
##   RNITEMS   generate N random deliveries; only secondary weight
##             set N as value of env['RNITEMS']


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


## pack-and-route:
##   - vehicles' data structure:
##     - X,Y coordinates
##     - earliest minute when they may leave (X,Y)
##     - list of all previous stops: this is the per-vehicle delivery plan
##
##   - scan each possible time window
##     - list deliveries which may happen in given time window
##       - find vehicles which may deliver within time window
##         - backtrack if (1) no later delivery windows and (2) no vehicle
##       - assign each capable vehicle+delivery minute; process rest
##       - save and compare overall quality for each complete solution
##
## backtrack-friendly data structure: store enough information to roll
## back all updates efficiently
##   - deliveries: store all other (delivery, vehicle) assignments
##     which were _not_ taken when assigning current one
##     - when backtracking, roll back currently assigned delivery and
##       vehicle assignmet, take next possible (delivery, vehicle) assignment
##   - vehicles: store pre-update (X,Y), previous earliest-minute tuple
##     - stops' list just pops last entry to backtrack


##=====  nothing user-serviceable below  =====================================
import csv, re, sys, os, operator, functools, itertools, time, json, copy
import socket               ## best-result reporting; ignores all write errors
import math, random
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

##-----  code generation  ----------------------------------
sCPREFIX = 'PCK'     ## common prefix for generated code (uppercase: public)
                     ##
sCDIST   = sCPREFIX.lower() +'_xy2dist'
                     ## name of xy->xy distances table, indexed by item index

sCGUARDVAR = sCPREFIX.upper() +'_INCLUDED__'        ## include guard variable

sCXYS      = sCPREFIX.lower() +'_xy_coords'  ## table of (x,y) pairs
sCXY_TYPE  = sCPREFIX.upper() +'_XYpair'     ## type(...table elements...)
sCXY_INIT0 = sCPREFIX.upper() +'_XYPAIR_INIT0'          ## 00-init all fields

sCORD_TYPE = sCPREFIX.upper() +'_Orders'     ## type(...order entries...)
sCORD_INIT0  = sCPREFIX.upper() +'_ORDERS_INIT0'          ## 00-init all fields

sCDELIVERIES = sCPREFIX.upper() +'_ORDERS'
                     ## number of orders, w/o removing any duplicate coordinates
sINDENT  = '    '    ## prefix added per indented level

sTABLE_BREAK = 10    ## add empty columns/rows every N units in large tables


##----------------------------------------------------------
## pack-and-route deliveries, special delivery/vehicle pairings:
##
## marker: not attempting delivery in currently evaluated window
vDELAY_DELIVERY = 'DELAY'
##
##   [ ...vehicle..., vDELAY_DELIVERY ] pairs list a delay as an
##   explicit entry in assign/backtrack list

## marker: assign new vehicle for this delivery
vNEW_VEHICLE = 'NEW.VEHICLE' 
##
##   since new vehicles lack history, only a single entry is needed,
##   without specifying which one


##----------------------------------------------------------
## BFD-scan parameters
##
## how many units of immediate future to consider, when checking for
## next-available candidates
vNEXTUNITS = 6


##----------------------------------------------------------
## trace types (bitmask)
vTRC_TIME  = 1
vTRC_MAP   = 2        ## map-related properties: coordinates, distances
vTRC_SCHED = 4        ## schedule-related properties: options when
                      ## assigning units to dispatch etc.
vTRC_STACK = 8        ## details of backtrace stack


##----------------------------------------------------------

TARGET = None        ## set to [ host, port ] if env specifies it

CRLF   = b'\n\r'     ## telnet official separator
COMM   = b'#'        ## prefix for commented log results

vTIME_UNIT_MINS = 15   ## how many minutes are in one time-vector unit
vTIME_UNDEF = 9E9      ## value for time vector meaning 'undefined' (=too high)
vTIME_DELIVER_MIN = 15    ## how many minutes to budget for one delivery
vAVG_MIN_PER_KM   =  5    ## fallback for average-speed calculation
## TODO: needs map scale

vHR_MAX = 18     ## max(schedule delivery), hours HH00
vHR_MIN =  8     ## min(schedule delivery), hours HH00


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
	...binpack blurb comes here...
	Usage: <MAX1=...> [MAX2=...] [PCT=...] [DEBUG=...]  ... <input list>
	...usage blurb comes here...
	""")


##--------------------------------------
tTRACETYPES = {
	'time':  vTRC_TIME,
	'map':   vTRC_MAP,
	'sched': vTRC_SCHED,
	'stack': vTRC_STACK,
}


##--------------------------------------
## caches parsed 'TRACE' env.variable
##
sys_trace = None


##--------------------------------------
## query and cache what has been marked to log by the 'TRACE' env. variable
##
def tracetypes():
	global sys_trace

	if sys_trace == None:
		sys_trace = 0
		if 'TRACE' in os.environ:
			for t in os.environ[ 'TRACE' ].split(','):
				if not t in tTRACETYPES:
					terminate(f"unknown trace type ({t})")
				sys_trace |= tTRACETYPES[t]

	return sys_trace


##--------------------------------------
## does the global 'DEBUG' setting, or optionally any of the trace
## types in 'trace', mean we want to log a current message?
##
def debug_is_active(lvl=1, trace=0):
	if DEBUG and (DEBUG >= 0) and (DEBUG >= lvl):
		return True

	return (trace & tracetypes())  if trace  else 0
			## nano-optimization to save calls to tracetypes()
			## please do not comment on it


##--------------------------------------
## returns False to allow set-log-passthrough chains
##
## 'type' is bitmask of vTRC... types, if specific event
## if any of these are enabled by 'TRACE', message is output
## regardless of debug level
##
def debugmsg(msg, lvl=1, type=0):
	if debug_is_active(lvl) or (type & tracetypes()):
		print(msg)

	return False


##--------------------------------------
## transform to human-scaled time
## start, end must have been supplied by time.perf_counter()
##
def timediff_str(start, end):
	diff  = end - start
	scale = 1000.0
	unit  = 'ms'

	return(f"{ diff * scale :.2f}{unit}")


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



##=====  delimiter: output formatting  =======================================
def comm(s, fmt='C'):
	return '/* ' +s +' */'


##--------------------------------------
def include_guard(start=True):
	guardvar = sCGUARDVAR

	if start:
		return(f'#if !defined({ sCGUARDVAR })' +'\n' +
		       f'#define  { sCGUARDVAR } 1  { comm("API version") }')

	return f'#endif   { comm("defined({ sCGUARDVAR })") }'


##--------------------------------------
tTIMEVEC = 'uint64_t'


##--------------------------------------
## struct ... { ... } field listing (field defs only)
##
## all-0 init in order_struct_all0(); keep these in sync
##
def order_struct_c(pts, const=True):
	return (
		sINDENT + ('const '  if const  else '')
			+f'struct { sCXY_TYPE } coords;',  ## -> order_xy_all0()
		'',

		sINDENT + 'unsigned int minute;    ' +
			comm('expected arrival, 1-based minute, >0 if known'),
		'',

		sINDENT + 'unsigned int vehicle;    ' +
			comm('assigned vehicle, 1-based index; ' +
				'0 when unknown'),
		'',

		sINDENT + f'{ tTIMEVEC } time_windows;',

		sINDENT + f'const char *time0;    ' +
			comm('human-readable delivery window/s'),
		'',

		sINDENT + f'unsigned int idx;    ' +
			comm("redundant, for context/debug"),
		'',

		sINDENT + f'unsigned int flags;',
	)


##--------------------------------------
## all0-init const for "struct { sCXY_TYPE }"
##
## mapped to " sCXY_INIT0 "
##
def order_xy_init0():
	return '{ 0, 0, }'


##--------------------------------------
## init const for field-list struct
## see order_struct_c()
##
def order_struct_init0():
##	return f'{{ { order_xy_init0() }, 0, }}'
	return f'{{ { sCXY_INIT0 }, 0, 0, NULL, 0, 0, 0, }}'


##--------------------------------------
## output table of XY points and their distances
## includes table-struct definitions
##
## with non-None 'pts', we output coordinate list (in commented-out
## explanatory table)
##
## input: see xy2table()
##
def xy2c(arr, pts=None):
	res = []
	if ((not 'points' in arr)  or
	    (not 'time' in arr)    or
	    (len(arr['points']) != len(arr['time']))):
		raise ValueError("invalid XY-to-XY distance setup")

	n = len(arr[ "points" ])

	res.append(f'#define  { sCDELIVERIES }  ((unsigned int) {n})')
	res.append('#include <stdint.h>')
	res.append('')

	res.extend([
		f'struct { sCXY_TYPE } {{',
			sINDENT + 'float x;',
			sINDENT + 'float y;',
		f'}} ;',
		'/**/',
		f'#define { sCXY_INIT0 } { order_xy_init0() }',
		'',
	])

				## struct for delivery-item list
	res.extend([
		'#if 0',
###		f'typedef struct { sCORD_TYPE } {{',
		f'struct { sCORD_TYPE } {{',
	])
	res.extend(order_struct_c(pts))
	res.extend([
###		f'}} *{ sCORD_TYPE }_t ;',
		f'}} ;',
		'/**/',
		f'#define { sCORD_INIT0 } { order_struct_init0() }',
		'#endif',
		'',
	])

	if pts:
		assert(len(pts) == n)

		xys = ', '.join(f'{{{x},{y}}}'  for x,y in pts)

		res.extend([
			'#if 0',
			'/* (X,Y) coordinates, in delivery-item order',
			f' * see { sCDIST }[] for point-to-point ' +
				'traversal cost',
			f' */',
			f'struct PCK_XYpair { sCXYS }[ { sCDELIVERIES } ' +
				f'/* {n} */ ] = {{',
			sINDENT + xys + ',',
			'} ;',
			'#endif',
			'',
		])

	res.extend([
		f'/* order-to-order costs, [i][j] == xy[i] -> xy[j] '
			'traversal cost',
		f' * see { sCXYS }[] for coordinate pairs',
		f' */',
	])

	d, cdigits = [], []
	maxd, mind = -1, 9999999999999

	for ri, row in enumerate(arr['time']):
		rowr = list(round(v)  for v in row)
		d.append(rowr)

		maxd = max(maxd, max(rowr))
		mind = min(mind, min(r  for r in rowr  if (r > 0)))

		if ri:
			cdigits = list(max(cdigits[ci], len(str(d[-1][ci])))
			               for ci in range(len(d[-1])))
		else:
			cdigits = list(len(str(val))  for val in d[-1])

			## column breaks
	colbrk = list([''] * len(d[0]))

	if sTABLE_BREAK:
		for i in range(len(d[0])):
			if i and ((i % sTABLE_BREAK) == 0) and (i < len(d)):
				colbrk[i] = ' '
## TODO: factor out, will be used by other array formatters

	res.extend([
		f'/* min(table>0)={ mind }; max(table)={ maxd }',
		' */',
	])

	res.append(f'static const uint32_t { sCDIST }' +
		f'[ {sCDELIVERIES} ][ {sCDELIVERIES} ] /* {n}x{n} */= {{')
		##
		## align all columns; cdigits stores per-column digit.count
		##

	for ri, row in enumerate(d):
		curr = ''.join(f'{row[ci] :>{ cdigits[ ci ] }},' +colbrk[ci]
		               for ci in range(len(row)))

		res.append(sINDENT +'{'+ curr +'},')

		if (sTABLE_BREAK and ri and ((ri % sTABLE_BREAK) == 0) and
		   (ri < len(d))):
			res.append('')

	res.append('} ;')
	res.append('')

	return('\n'.join(res))


##=====  /delimiter  =========================================================


##---------------------------------------
## returns 'defval' if key is not present in environment, or is non-numeric
## does not raise exceptions
##
def env2num(key, default=None, expect_float=False):
	n = default
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
			## deliveries lacking delivery window have min.time=0
	mn = min(a[ 'min_time' ] for a in aux  if a[ 'min_time' ])
	mx = max(a[ 'max_time' ] for a in aux)

	for a in aux:
		a[ 'MIN_TIME_ALL' ] = mn
		a[ 'MAX_TIME_ALL' ] = mx


##--------------------------------------
def unitindex2vectorbit(u):
	"map 0-based time-unit index to corresponding"

	return 1 << u


##--------------------------------------
## maps HHMM-HHMM[+...] strings to bitvector, with each bit corresponding
## to 'twindow' minutes
##
## returns [ vector, min.bit(vector), max.bit(vector), ]
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
	vec, minv, maxv = 0, vTIME_UNDEF, 0
				## minv is 'arbitrary large enough value'

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
					## 0000-2400, 'any suitable time'
			if (sm == sh == sm == 0) and (eh == 24):
				continue
					## RRR: deal with optional deliveries
			else:
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

		minv = min(su, minv)
		maxv = max(eu, maxv)

		vec |= unitindex2vectorbit(eu) - unitindex2vectorbit(su)
		## XXX ((1 << eu) - (1 << su)

	if minv == vTIME_UNDEF:
		minv = 0

	if maxv == 0:
		return [ 0, 0, 0, ]

	return vec, 1 << minv, 1 << (maxv -1)


##--------------------------------------
## read back XY-to-distance lookup table
## only checking subsequently: table is retrieved before deliveries are read
##
def json2distances(fname):
					## TODO: proper exception handling
	try:
		tab = json.load(open(fname, "rb"))
	except:
		sys.stderr.write("Unable to read XY-to-distance table " +
				f"({ fname })\n")
		return None

	return tab


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
## autodetects basic/extended input; returns List Auxiliary Data as:
## [
##   {
##     'index':    ...original index in input...,
##     'primary':  ...primary parameter...
##     'secondary':  ...secondary parameter...
##     'time':     '0845-0945+1015-1115',
##     'minutes':  actual arrival, 0-based minutes from vHR_MIN:00
##     'vehicle':  ...vehicle ID...
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
##     'window':  preferred window, such as generated by an initial assignment,
##                before actual arrival time is set.  may not be set.
##
##     'min_time': 0x8,
##     'max_time': 0x1000,
##                  -- LS, MS bit in bitmask
##                  -- used for fast 'X must happen before Y' comparisons
##     'time_units': Hamming weight of 'time2vec'     -- save .bitcount() calls
##
##                  -- globals replicated to each record
##                  -- (to allow local key function eval, things like that)
##     'MIN_TIME_ALL': global min-time for all deliveries (time vector)
##     'MAX_TIME_ALL': ... max-time ...
##     'x': ...coordinate... (None if unknown)
##     'y': ...coordinate...
##     'start': ...             -- initial delivery time, minutes, subject
##                              -- to refinement
##     'seen': '1240',          -- if set and non-empty, delivery time (string)
##     'svec': x40000,          -- time vector form of 'seen', if non-empty
##
## flags-like variables:
##     'optional': ...          -- is it OK to skip this delivery?
##                              -- low-priority, 'deliver if possible today'
##     'is_final': ...          -- has this delivery been frozen?
##                              -- has both 'minutes' and 'vehicle' set,
##                              -- no more changes
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

			if (mint == 0):
				sys.stderr.write("No delivery window:\n" +
					f"    '{ f }'")

			x, y = f[2], f[3]
					## any conversion etc. would come here

			aux.append({
				'primary':    fd1,
				'secondary':  fd2,
				'time':       f[4],          ## original string
				'time2vec':   t,
				'time_units': pathtools.bitcount(t),
				'index':      fi,
				'min_time':   mint,
				'max_time':   maxt,
				'x':          x,
				'y':          y,
			})
			if False:
				aux[-1][ 'optional' ] = True

	res = sorted(res, key=functools.cmp_to_key(table_cmp))

	if (itype == 'extended'):
		aux2plus(aux)

	return res, aux


##--------------------------------------
## BFD ordering: return two groups, one selected by best-fit-decreasing,
## one containing all rejected records
##
## input has been decreasing-sorted by primary column
## uses basic format, extended with input-index:
##     [ <primary>, <secondary>, <identifier>, <input index> ] tuples
##
## 'sum1' and 'sum2' just avoid sum() calls; may replace (expect small N)
## since BFD does not backtrack, these increase-only sums are sufficient
##
## check for early termination with max.elems
## since BFD only looks at largest entries, if we hit the limit here,
## that is our achievable optimum
##
## see also: best_fit_decreasing_multiple(), a wrapper around this
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

		if debug_is_active(2):
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
## (used to cache sums of lengths etc., skipping floats)
##
## separator not expected to interfere with CSV (excludes ","),
## un/signed numbers (excludes "-" and "+")
##
def tuple2idxstring(tuple):
	"itertools....-returned tuple to dict-index-ready string form"
	return ":".join(str(t) for t in tuple)


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
## sort deliveries in order of urgency; usable as .sort() key function
##   - earliest delivery time
##   - secondary: latest delivery time
##   - third:
##   - fourth: increasing order of nr. of possible delivery slots
##
## see 'List Auxiliary Data' for input structure
##
## construct (min.time << N) | (max.time) with sufficient field width
## for fields not to overlap.
##
def del_timesort(d):
	"sort: key function for deliveries: decreasing urgency"

				## MXB, NRB are bits of max-time, nr-of-slots
				## fields, respectively
				##
				## both rounded up to full bytes, so
				## fields become hex-value visible

	mn, MXB = d[ 'min_time' ], pathtools.bitcount(d[ 'MAX_TIME_ALL' ])
	nrbits = pathtools.popcount(d[ 'time2vec' ])

			## max(bits(time2vec)) <= bits(d[ 'MAX_TIME_ALL' ])
			## how many bytes are sufficient to represent
			## nr. of 1 bits?
	NRB = (MXB +255) // 256

	MXB = (MXB +7) // 8             ## now in bytes

	MXB, NRB = MXB *8, NRB *8       ## back to bits

	rv = (mn << (MXB +NRB)) | (d[ 'max_time' ] << NRB) | nrbits

	return rv


##--------------------------------------
## sort deliveries in increasing-delivery order; usable as .sort() key function
## tolerate entries which lack the 'start'; schedule those in the end
##
def del_unit2sort(d):
	"sort: key function for deliveries: recommended start time"
	rv = 0

	rv = (d[ 'start' ] << 48)  if ('start' in d)  else 0

						## ~arbitrary tiebreakers
	rv += d[ 'time_units' ] << 24
	rv += d[ 'index' ]

	return rv


##--------------------------------------
## TODO: consolidate to a single representation, then remove/inline
##
def xy2dist(x, y, x0, y0, wgt=1.0):
	d = (x - x0) ** 2 + (y - y0) ** 2
	d = math.sqrt(d)

	return d * wgt


##--------------------------------------
def xy2time(x, y, x0, y0, wgt=1.0, start_minutes=None):
	d = xy2dist(float(x), float(y), float(x0), float(y0))

			## crude avg. speed
## TODO: ASSUMES CONSTANT SPEED
## TODO: NEED MAP SCALE

	return vAVG_MIN_PER_KM * (d * 15)


##--------------------------------------
## returns [ src.index ][ dest.index ] list of XY distances
## bases are appended after delivery points
##
## sets string-indexed values to 'xys' if non-None
##
## x0, x1, ... are string variables; xs/xd are source/dest numeric values
##
def distances(deliveries, bases, wgt=1.0, xys=None, idx=True):
	points = deliveries[:]
	for b in bases:
		points.append({             ## force floats to canonical string
			'x': str(b[0]),
			'y': str(b[1]),
		})

	arr = [0] * len(points)
	arr = list(arr for r in range(len(arr)))

	for si, src in enumerate(points):
		x0, y0 = float(src['x']), float(src['y'])
		xs, ys = float(x0), float(y0)

		for di, dst in enumerate(points):
			if si == di:
				continue

			x1, y1 = float(dst['x']), float(dst['y'])
			xd, yd = float(x1), float(y1)

			d = xy2dist(xd, yd, xs, ys, wgt=wgt)

			arr[ di ][ si ] = d
			arr[ si ][ di ] = d

			if xys != None:
					## single index combining X+Y
				sxy = tuple2idxstring([x0, y0])
				dxy = tuple2idxstring([x1, y1])

					## TODO: check dict/default value
					## Python-version compatibility
					##
				if not sxy in xys:
					xys[ sxy ] = {}
				xys[ sxy ][ dxy ] = d
					##
				if not dxy in xys:
					xys[ dxy ] = {}
				xys[ dxy ][ sxy ] = d
	return arr


##--------------------------------------
def minute2timevec(m):
	"0-based minutes, relative to start, to timevector/bitmask"
	return 1 << (m // vTIME_UNIT_MINS)


##--------------------------------------
def minute2wall(m):
	"0-based minutes to 24-hour wall-clock time [string]"
	m += vHR_MIN * 60

	return f"{ m //60 :02}{ m %60 :02}"


##--------------------------------------
def minute2vecbefore(m):
	return minute2timevec(m) -1


##--------------------------------------
def timevec2after(t, maxunits):
	"bitmask: all units strictly after all max(units(t))"

	return ((1 << maxunits) -1) - ((1 << pathtools.bitcount(t)) -1)


##--------------------------------------
## earliest unit/minute of time vector
## 0 if vector is empty
##
## returns minutes relative to vHR_MIN with True 'minutes', rounded
## to LS point of time vector (so x1 -> minutes=0, x10 -> minutes=60)
##
def timevec2asap(t, minutes=False):
	if t == 0:
		return 0

	lsb = t ^ (t & (t - 1))

	if minutes:
		return vTIME_UNIT_MINS * (pathtools.bitcount(lsb) -1)

	return lsb
			## ... & (t-1) removes LS one bit


##--------------------------------------
## visualizes time bitmask
## returns left-to-right time diagram
##    ---  unused
##    ###  used, travel (rounded up)
##    |||  used, transfer (rounded up)
##
## 'unitcols' specifices number of columns per unit
##
def timevec2utilstr(timevec, maxunits, unitcols=3, sep=' ', sep2=0):
	used, transf, empty = '#', '|', '-'
	used, transf, empty = used *unitcols, transf *unitcols, empty *unitcols

	arr = []
	for t in range(maxunits):
		if ((1 << t) & timevec):
			if False:
				arr.append(transf)
			else:
				arr.append(used)
		else:
			arr.append(empty)

			## collate every N columns (TODO)
	if sep2:
		pass

	return sep.join(arr)


##--------------------------------------
## Vehicle Status
##
## 'V.ID': {
##    'stops':    [ [ minute, delivery ID, X, Y, ],
##                  [ minute(2), del.ID(2), X(2), Y(2), ]... ]
##                X,Y fields are redundant; please do not comment on it
##                TODO: mark fields etc.
##    'time':     nominal departure time, 'HHMM'
##    'tvec':     nominal earliest departure time, vector
##  ##  'time_max': ...earliest arrival...    if defined
##  ##  'time_min': ...latest departure...    if defined
##    'x':        X coordinate, current
##    'y':        Y coordinate, current
##    'idx':      index of current point, if not None
##    'primary':     sum of primary fields in already scheduled deliveries
##    'secondary':   ...secondary fields...
##    'refills':  chronologically increasing list of refill time vectors
##    'deliveries': { time: order.index, ... }
##
##    'START.X':    X coordinate, start of deliveries
##    'START.Y':    Y coordinate...
##    'START.MINS': 0-based minute
## }


##--------------------------------------
## TODO: Python version-portable automatic values
##
def vehicle2primary(vehicle):
	return  vehicle[ 'primary' ]  if ('primary' in vehicle)  else 0


##--------------------------------------
## TODO: Python version-portable automatic values
##
def vehicle2secondary(vehicle):
	return  vehicle[ 'secondary' ]  if ('secondary' in vehicle)  else 0


##--------------------------------------
## updates 'vehicles', routing vehicle with ID 'v' to (x, y) with
## (changes restricted to 'vehicles[v]')
##
## nominal arrival 't' (minutes)
##
## notes time of _arrival_ at position
##
## returns updated vehicle record only with False 'update'
##
def vehicle2xy(vehicles, v, minutes, delivery, update=True):
	"register moving a vehicle (v) to XY at time T"

	if (not vehicles) or (not v in vehicles):
		raise ValueError(f"unknown vehicle '{v}'")

	x, y  = delivery['x'], delivery['y']
	nv    = {}
	currv = vehicles[v]

	v_from = ''
	if ('x' in currv) and (currv['x'] != None):
		v_from =  f'from X={ currv["x"] }'
		v_from += f',Y={ currv["y"] }'

	had_prev_xy = ('x' in currv)

	nv[ 'minutes' ] = minutes
	nv[ 'tvec'    ] = minute2timevec(minutes)
	nv[ 'x'       ] = x
	nv[ 'y'       ] = y

	nv[ 'primary'   ] = vehicle2primary(currv)   + delivery[ 'primary'   ]
	nv[ 'secondary' ] = vehicle2secondary(currv) + delivery[ 'secondary' ]
		##
		## assertion: no overruns

	nv[ 'deliveries' ] = {}
	nv[ 'deliveries' ][ minutes ] = delivery[ 'index' ]

	print(f'## ARRIVE[{v}]={ minute2wall(minutes) } X={x},Y={y} ' +
	      f'{ v_from }[idx={ delivery["index"] }] +' +
	      f'{ delivery[ "primary" ] }')
	print(f'## LOAD.TOTAL[{ v }]={ nv[ "primary" ] }')

	if not had_prev_xy:
		nv[ 'START.X'    ] = x
		nv[ 'START.Y'    ] = y
		nv[ 'START.MINS' ] = minutes

	if update:
		vehicles[v] = nv

	return nv


##--------------------------------------
## map vehicle refill time strings to time vectors
##
## example:
##     { 'V0': {                  ## refill windows for V0:
##          '1600-1700',
##          '1200-1300+1400-1500',
##       },
##     }
## ->
##     { 'V0': {
##          'times':   [ '1200-1300+1400-1500', '1600-1700', ],
##          'timevec': [ 0xf0f0000, 0xf00000000, ],
##       },
##     }
##
def vehiclerefills(vrefill):
	refills = {}

	for v in vrefill:
		if not v in refills:
			refills[v] = {
				'times':   [],
				'timevec': [],
			}
		addtimes, vectimes = [], []

		for t in sorted(vrefill[v]):
			tvec = times2vec(t)[0]
			try:
				addtimes.append(t)
				vectimes.append(tvec)
			except:
				raise ValueError(f"bad refill window '{t}'")

		refills[v][ 'times'   ].extend(addtimes)
		refills[v][ 'timevec' ].extend(vectimes)

	return refills


##--------------------------------------
## calculate back start time at (x0, y0) which reaches (x, y) by 'time'
##
def initial_delivery2starttime(x, y, timevec, x0, y0):
	return '0000'


##--------------------------------------
## ASAP minute of reaching (x, y) from (x0, y0), optionally within window 't'
## returns None if delivery may never hit time window
##
## 'now' is (ASAP) start time, excluding delivery overhead (== arrival
##       at preceding delivery)
## filters against 't' as a time vector, if value is not None
##
def xy2asap_minute(x0, y0, x, y, now, t=None):
	dt = xy2time(float(x), float(y), float(x0), float(y0))

			## arrival did not account for overhead; add here
	dt = round(dt + vTIME_DELIVER_MIN)

	wt = minute2timevec(dt)

	if t:
		aw = wt | timevec2after(wt, maxtb)
				## arrival window: <= arrival <= end(timevec)
		aw &= t
		if aw == 0:
			return None

	return timevec2asap(aw, minutes=True)


##--------------------------------------
## return vehicles which can reach (x, y) within timevec from
## their current position
##   - returns [vehicle, distance, ASAP arrival, timevec of possible arrival]
##     in increasing-ASAP order
##   - sort hits earliest to latest
##   - only add one generic 'new vehicle' entry (-> vNEW_VEHICLE)
##
## 'vehicles' is Vehicle Status
## 'dists' is index/XY-to-index/XY distance lookup table
## 'assign_new' controls whether new vehicles are assigned here
##              (alternate: callers may assign selectively)
##
## 'delivery' would be, at some point, used to filter delivery/vehicle pairs
##
## uses string-indexed distances' table
##
def vehicle_may_reach(x, y, timevec, vehicles, dists, delivery,
                      assign_new=True):
	res   = []
	maxtb = pathtools.bitcount(timevec)
	new   = 0          ## how many newly assigned vehicles (no history)
	                   ## have been seen?

	for vi, v in enumerate(vehicles):
		if (not assign_new) and (not 'x' in vehicles[v]):
			continue                ## unassigned vehicle, ignore

						## new vehicle: no history
		if (((not 'x' in vehicles[v]) or (not 'minutes' in vehicles[v]))
		    and assign_new):
			if new < 1:
				t = timevec2asap(timevec, minutes=True)
				res.append([ vNEW_VEHICLE, 0.0, t, timevec, ])
			                       ## 'immediate start' placeholder
			new += 1
			continue               ## assume vehicle start
			                       ## updated later to
			                       ## accommodate delivery

		x0, y0 = float(vehicles[v]['x']), float(vehicles[v]['y'])

		t = xy2asap_minute(x0, y0, x, y,
		              vehicles[v]['stops'][-1][ 0 ],
## TODO: [0] is minutes field; mark properly
		              t=timevec)
		if t == None:
			continue        ## can not hit any suitable window

## factor out: almost identical to generic xy-to-ASAP.arrival check loop
##		dt = xy2time(float(x), float(y), float(x0), float(y0))
##
##					## current v[...] time excludes delivery
##					## time; account for it now
##		dt = round(dt + vTIME_DELIVER_MIN)
##
##					## does arrival time fit within delivery
##					## window at all?
##		wt = minute2timevec(dt)
##		aw = wt | timevec2after(wt, maxtb)
##				## arrival window: <= arrival <= end(timevec)
##		aw &= timevec
##		if aw == 0:
##			continue            ## can not reach within time vector
##
##		t = timevec2asap(aw, minutes=True)
## /factor out

		dist = xy2dist(float(x), float(y), float(x0), float(y0))

		res.append([ v, dist, t, wt, ])
		continue
		print('')
						## sort by ASAP arrival
	res.sort(key=operator.itemgetter(2))

	return res


##--------------------------------------
def timevec2units(tvec):
	"generator, returning each unit present in 'tvec' in increasing order"

	while tvec:
		lsb   = tvec ^ (tvec & (tvec - 1))
		tvec &= ~lsb
		yield lsb


##--------------------------------------
## find reasonable initial values for delivery-time search
## sets 'window' to these initial values
##
## sets 'start' for yet-uninitialized entries
##
## strategies:
##   0  place start times as far as feasible
##
## requires MIN_TIME_ALL/MAX_TIME_ALL to be set for all entries
##
def starttimes(dels, strategy=0):
	cds = list(d  for d in dels
	           if (d['time2vec'] != 0) and (not "start" in d))

				## collect 'certain' (already assigned) and
				## possible (possibly valid in T=...) load
				##
	minu, maxu = dels[0][ 'MIN_TIME_ALL' ], dels[0][ 'MAX_TIME_ALL' ]
	minu, maxu = pathtools.bitcount(minu), pathtools.bitcount(maxu)

	certain  = [0] * (maxu +1)
	possible = [0] * (maxu +1)

	for d in cds:
		ulist = list(1 if (d['time2vec'] & (1 << (u-1))) else 0
		             for u in range(minu, maxu))
					## TODO: store list form in addition
					## to time2vec during init
		d['units'] = ulist

	for u in range(len(ulist)):           ## reuse loop var falling through
		possible[u] = sum(float(d['units'][u]) / d['time_units']
		                  for d in cds)

## factor out, reuse as timeline-to-chart
					## sketch rough possible-utilization
	maxp, plines = max(possible), []
					## plot 20+1 char utilization
			##
	print("## Approximate possible utilization as a function of time")
	for i in possible:
		lvl = round((20.0 * i) / maxp)
		lvl = ('.' * lvl) +'#' +(' ' * (20 -lvl))
		plines.append(lvl)
			##
	for i in range(len(plines[0])-1, -1, -1):
		print("##    |", ''.join(pl[i]  for pl in plines))
	print('')

					## TODO: initial assignment, in
					## least-to-most available units order
	for d in cds:
		du = d['units']
		pu = list(possible[ui] + certain[ui]  if (du[ ui ])  else 0
		                        for ui, u in enumerate(du))

		smn = min(s  for s in pu  if s>0.0)

							## where is minimum>0?
		si  = list(i  for i in range(len(du))  if (pu[i] == smn))

					## TODO: sets multi-interval 'window'
					## through si-to-vector

		if len(si) != 1:
			si = [ si[0] ]
					## multiple optimal starting units
					## TODO: workaround: picking first one
		si = si[0]

		print(f"## SET.INITIAL unit={ si } idx={ d['index'] } " +
		      f"T={ d['time'] } MIN(UTIL)={ smn :.06}")
				##
		print("##     TW=" +timevec2utilstr(d[ 'time2vec' ],
		                                    maxu, sep='', unitcols=1))
		print("##    D.0=" +timevec2utilstr(1 << si,
		                                    maxu, sep='', unitcols=1))

					## move weighted probable entries
					## to 1-weight fixed ones
					##
					## remove-weight of current delivery
		rwgt = 1.0 / d['time_units']

		for ui, u in enumerate(d['units']):
			if u:
				possible[ui] -= rwgt

					## at least currently in unit 'si'
		certain[si] += 1
		d[ 'start'  ] = si
		d[ 'window' ] = unitindex2vectorbit(si)

	print('## UTIL.0', ",".join(str(c) for c in certain))
	print(f'## MIN(UTIL.0)={ min(c  for c in certain  if (c>0)) }')
	print(f'## MAX(UTIL.0)={ max(certain) }')
	print('')


##--------------------------------------
## filter vehicle IDs which may pick up delivery
##
## returns list of [vehicle ID, earliest arrival] tuples
##
## does not trim 'newly assigned vehicles' list; expect caller to do that
##
## 'new_load' is [primary, secondary] tuple
## 'vpos'    is vehicle-position vector
## 'minute0' is earliest minute to register for newly assigned vehicles
##
def vehicles_which_may_deliver(new_load, vehicles, vpos, minute0=0):
	primary, secondary = new_load

	if vehicles == []:
		return []     ## would do below, after some bookkeeping

	res = []
	for v in vehicles:
		vid = v[0]

		if (vid == vNEW_VEHICLE):
			res.append([ vid, minute0, ])
			continue

		v1  = vehicle2primary  (vpos[ vid ])
		v2  = vehicle2secondary(vpos[ vid ])

		if (primary +v1) > MAX1:
			print(f"##   V.OVERLOAD[{ vid }]: " +
			      f"{ primary + v1 }")
			continue

		if MAX2 and ((secondary +v2) > MAX2):
			print(f"##   V.OVERLOAD.SECONDARY[{ vid }]: " +
			      f"{ secondary + v2 }")
			continue

		res.append([ vid, v[2], ])

	return res


##--------------------------------------
def msbit(t):
	return (1 << (t.bit_length() -1))


##--------------------------------------
def has_time_after(d, t):
	"may this delivery be completed after time window?"

	if d and ("time2vec" in d):
					## possible delivery times, minus any
					## bits of 't' or before
		t = msbit(t)

		dminust = d[ "time2vec" ] & ~(t + t -1)

		return (dminust > 0)

	return False


##--------------------------------------
## input is aux.data struct for delivery
##
def btrack_delivery(d, delay=False):
	"data structure to back up delivery 'before' state (backtrack form)"

	res = {
		'type': 'DELIVERY',
		'data': {
			'id':       d[ 'index'    ],
			'time2vec': d[ 'time2vec' ],
		}
	}

	if delay:
		res[ 'delayed' ] = True

	return res


##--------------------------------------
## input is 'Vehicle Status' struct for vehicle
## stores ID of delivery if known
##
def btrack_vehicle(v, vid, delivery=None):
	"data structure to back up vehicle 'before' state (backtrack form)"

	vraw = copy.deepcopy(v)                       ## resolve all references

	res = {
		'type': 'VEHICLE',
		'id':   vid,
		'data': vraw
	}

	if delivery:
		res[ 'orderid' ] = delivery[ 'index' ]

	return res


##--------------------------------------
## raises exception if
##   - vehicles MUST reference controlling delivery (if 'orderid' present)
##   - deliveries which lack vehicles MUST be marked as delayed
##     - exception: last entry is delivery; assume corresponding
##       vehicles have not yet been entered as 
##
def list_backtrack(bt):
	"format and parse back current backtrack state"

	for bi, b in enumerate(reversed(bt)):
		pass
## pretty-print(backtrace) comes here


##--------------------------------------
def is_delivery_frozen(d):
	return (('minutes' in d) or
	        (('is-final' in d) and d[ 'is_final' ]))
##
## TODO: finalize logic


##--------------------------------------
## returns decreasing-quality list of BFD index collections
## input is array of index-extended basic form entries
##
## returns list of list-of-indexes with sum(primary) appended
##
## avoid changing 'tbl'
##
def best_fit_decreasing_multiple(tbl):
				## try BFD plans as an approximation of
				## how many vehicles are needed
	tbl = copy.deepcopy(tbl)
	res = []
	sel = [ None, ]

	while sel:
		sel, tbl = best_fit_decreasing(tbl, MAX_ELEMS)

		if sel:
			res.append(sel)

	return res


##--------------------------------------
## returns pretty-printed ID of vehicle if recognized as special
##
def is_special_vehicle(v):
	"is this delivery(tuple) for a special 'vehicle' (delay etc.)?"

	if (v == vNEW_VEHICLE):
		return '[new vehicle]'

	elif (v == vDELAY_DELIVERY):
		return '[deliver later]'

	return False


##--------------------------------------
## human-readable form for special assignments
##
def delvtuple2str(v, asap):
	"pretty-print [ vehicle, time(ASAP), ] tuples"

	vs = is_special_vehicle(v)

	return f'V[,ASAP={ asap }min]'  if not vs  else vs


##--------------------------------------
## generate all combinations of assignments
##
## 'avail_new' is number of yet-unassigned new vehicles
## 'may_delay' contains delivery index (value>0) if it may be started
##             in later unit
##
def vehicle_assignments(didxs, curr, t0, avail_new, may_delay):
	valid = []
	for di in didxs:
		valid.append([ di, curr[di] ])

	if avail_new == 0:
		yield itertools.product(valid)
	else:
		return []

	return []
##
## TODO: use Gray code for minimal incremental changes


##--------------------------------------
def virtual_vehicle2id(nr):
	return f'VEHICLE{nr:02d}'


##--------------------------------------
def mayreach2str(t):
	"pretty-print vehicle ID, primary, ASAP tuples"

	if len(t) == 2:
		return f'[id={ t[0] },primary={ t[1] }]'

	return f'[id={ t[0] },primary={ t[1] },ASAP={ t[2] }min]'


##--------------------------------------
def new_vehicle(vid):
	"Vehicle Status struct for newly assigned one"

	return {
		'primary':   0,
		'secondary': 0,
		'deliveries': {},
		'refills':    [],
		'stops':      [],     ## schedule form of deliveries{}
	}


##--------------------------------------
## passed parsed coordinate+time-equipped delivery plan, and base list
## enumerate possible base-start times and reachable schedules
##
## 'aux' and 'bases' must have been initialized, not empty
## 'vehicles' is list of initial vehicle positions, 'None' for not-yet-defined
##
## 'asap' and 'alap' prefer as-soon-as-possible or as-late-as-possible
## schedules, if feasible. (may specify both; interaction is undefined)
##
## iterator: keeps returning improving schedules
##
## creates new plan with [] (default)
## perturbs existing one if passed non-[]
##
def pack_and_route(deliveries, aux, bases, vehicles, vrefill=[], plan=[],
                   xy2d=None, asap=False, alap=False):
	sched, place, vpos, decisions = [], [], {}, []
	minutes_now = 0
				## vpos is vehicle positions, if already known

	if len(deliveries) != len(aux):
		raise ValueError("inconsistent delivery+aux data")
	if not aux:
		raise ValueError("aux.data is uninitialized")

				## time vector: all scheduled delivery windows
	alltime_v = 0
	for d in aux:
		alltime_v |= d[ 'time2vec' ]

	refills = vehiclerefills(vrefill)
	vlist   = sorted(refills.keys())                ## list of vehicles/IDs

	vpos = {}
	for v in vlist:
		if not v in vpos:
			vpos[v] = {}
	for v in refills:
		if not v in vpos:
			vpos[v] = {}
	## initial vehicle list

	maxu = max(pathtools.bitcount(d[ 'MAX_TIME_ALL' ])  for d in aux)

	for v in sorted(refills.keys()):
		for tvec in sorted(refills[v][ 'timevec' ]):
			print(f"## FILL[{v}]=" +timevec2utilstr(tvec,
			                        maxu, sep='', unitcols=1))
	print()
				## compulsory refill windows

				## calculate distances between delivery points
				## and bases, unless already loaded as table
	if xy2d == None:
		xy2d = {}
		dist = distances(aux, bases, xys=xy2d)

	##-----  initial BFD-based estimate  ---------------------------------
	## how many vehicles could deliver, just by iteratively picking
	## BFD plans for them, w/o any delivery-time or distance
	## considerations?
	##
	## this plan is obviously unrealistic, but it gives us
	## an initial estimate to plan for. we do not expect this
	## many vehicles to be able to deliver---in other words,
	## this is our minimal-count plan.


	tstart = time.perf_counter()

				## try BFD plans as an approximation of
				## how many vehicles are needed
	bfds = best_fit_decreasing_multiple(tbl)
	debugmsg(f'## BFD.VEHICLES={ len(bfds) }', 1)

	tend = time.perf_counter()
	debugmsg(f'## time(BFD.VEHICLES)={ timediff_str(tstart, tend) }',
	         lvl=2, type=vTRC_TIME)
	tstart = tend
	##-----  tstart is after nr-of-units(BFD) calc  ----------------------


	##-----  v1:  --------------------------------------------------------
	## greedy-assign routes for one vehicle at a time, in a BFD fashion:
	##   - pick the next few delivery windows
	##   - pick yet-unassigned deliveries; decreasing-sort them
	##   - loop across 'reasonable subset' of possible deliveries:
	##     - route vehicle to candidate; mark candidate as served
	##       route vehicle to position (ASAP)
	##     - accommodate special deliveries, such as 'must return to base'
	##       these generally have priority over any delivery
	##
	## heuristic settings:
	##   1) how many units of immediate future to consider (vNEXTUNITS)

	dels = copy.deepcopy(aux)

	tmin, tmax = dels[0][ 'MIN_TIME_ALL' ], dels[0][ 'MAX_TIME_ALL' ]

				## vplans: v.route info, see 'Vehicle Status'
	vplans, done = {}, False

				## brute-force plan generation for each
				## vehicle, based on BFD approximation
	while not done:
		t   = tmin
		vid = virtual_vehicle2id(len(vplans))

		vplans[ vid ] = new_vehicle(vid)

		debugmsg(f'## PLAN.VEH.NR={ len(vplans) }', 2,
		         type=vTRC_SCHED)

			## redundant copies of vplans[] fields
		primary, x, y = 0, None, None

					## scan yet-unassigned deliveries which
					## may be started in [t .. t+vNEXTUNITS)
		while (t <= tmax):
			t0 = timevec2asap(t, minutes=True)
			te = t0 + vTIME_UNIT_MINS * vNEXTUNITS -1
			tmask = (t << vNEXTUNITS) -t

					## minute of previous arrival,
					## excluding delivery overhead
			if (x == None) or (vplans[vid]['stops'] == []):
				arrived = None
			else:
				arrived = vplans[vid][ 'stops' ][-1][0]
## TODO: symbolic const for [0] -> index-of-minutes

			debugmsg(f'## T.WINDOW={ minute2wall(t0) }..' +
				 f'{ minute2wall(te) }', 1)
			debugmsg(f'## T.WINDOW.X=x{ tmask :x}', 1)

						## which deliveries
						## (1) may be scheduled here?
						## (2) are not yet assigned
						## (3) does not overload vehicle
			ds = list(d  for d in dels
				if ((tmask & d[ 'time2vec' ]) and        ## (1)
				    (not is_delivery_frozen(d))))        ## (2)

						## 'may reach'
						## (index, primary) tuples in
						## decreasing primary order
						##
			mr = sorted(([ d["index"], d["primary" ], ]
		 	        for d in ds
			        if (d["primary"] +primary <= MAX1)),     ## (3)
			        key=operator.itemgetter(1), reverse=True)
##
## TODO: filter directly using xy2asap_minute(), which is now
## replicated below

			debugmsg('## SCHED.NOW.CHECK0=' +
			         ','.join(mayreach2str(m) for m in mr),
			         2, type=vTRC_SCHED)

					## turn [ idx, primary ] to
					## [ index, primary, ASAP(minute) ]
					## tuples

			if x != None:
				mrn = []
				for di, add in mr:
					asap = xy2asap_minute(x, y, x, y,
					        arrived, dels[di][ 'time2vec' ])
					if asap == None:
						continue       ## can not reach
					mrn.append([ di, add, asap ])

			else:
					## starting new vehicle: assume it
					## can reach by start of window
					##
				mrn = list([ di, add,
					timevec2asap(dels[di][ 'time2vec' ],
					             minutes=True), ]
				        for di, add in mr)
			mr = mrn

			debugmsg('## SCHED.NOW.CHECK=' +
			         ','.join(mayreach2str(m) for m in mr),
			         2, type=vTRC_SCHED)

			for id, pr, asap in mrn:
				debugmsg(f"## ASSIGN.V[V={vid},DEL={id}]=" +
				         f"{asap}min",
				         1, type=vTRC_SCHED)
				pass

			t <<= vNEXTUNITS

		done = True


	##-----  v2:  --------------------------------------------------------

				## pick "reasonably spaced" start times for
				## all deliveries
	dels = copy.deepcopy(aux)

	tstart = time.perf_counter()
	starttimes(dels)
	tend = time.perf_counter()
		##
	debugmsg(f'## time(START.TIMES)={ timediff_str(tstart, tend) }',
	         lvl=2, type=vTRC_TIME)
	tstart = tend
	##-----  tstart is after initial delivery assignments  ---------------


	tmin, tmax = dels[0][ 'MIN_TIME_ALL' ], dels[0][ 'MAX_TIME_ALL' ]
	t = tmin

	backtrack  = []         ## assigned in each turn
	btrack_alt = []         ## alternates to those assigned in each turn
	                        ## MUST evolve in matched pairs

	avail   = len(vpos)     ## number of new vehicles one may assign
	delayed = {}            ## anything pushed back in current schedule

	vpos0 = copy.deepcopy(vpos)

				## enumerate delivery windows (bits in mask)
				## in chronological order
	while (t <= tmax):
		assert(len(backtrack) == len(btrack_alt))      ## matched pairs

		t0 = timevec2asap(t, minutes=True)
		te = t0 + vTIME_UNIT_MINS -1
		tunit = t.bit_length()-1               ## 0-based, from tmin...
		t += t             ## current t is t/2; allow simple continue

		debugmsg(f'## T.WINDOW={ minute2wall(t0) }..' +
			 f'{ minute2wall(te) }', 1)

		##---  enumerate all possible (delivery, vehicle) pairs  -----
		## (1) 'new vehicle' assignment appear, once, if new vehicles
		##     may still be added/assigned
		## (2) delay listed as 'vehicle' if still possible

						## which deliveries have
						## been pre-scheduled here?
		ds = list(d  for d in dels
			if (('window' in d) and (t & d['window']) and
			    (not is_delivery_frozen(d))))

		didxs = list(sorted(d[ "index" ] for d in (ds)))

					## which one of the delayed deliveries
					## may be considered in this time unit?
					##
		ddelay_now = list(d  for d in delayed.keys()
		                  if ((t & dels[d][ 'window' ] and
		                      not is_delivery_frozen(dels[d]))))
					##
		ddelay_now = list(sorted(ddelay_now))

		if debug_is_active(3, vTRC_SCHED):
			print('## BACKTRACK.TAKEN ', backtrack)
			print('## BACKTRACK.ALT   ', btrack_alt)
					## backtrack stack at entry

		if debug_is_active(2, vTRC_SCHED):
			print('## SCHED.INIT0.NOW    ', didxs)
			if ddelay_now:
				print('## +BACKTRACK.DELAYED ',
				      ",".join(str(di)
				          for di in sorted(ddelay_now)))

		didxs.extend(ddelay_now)
		didxs = list(sorted(didxs))   ## anything possibly starting now

		if debug_is_active(2, vTRC_SCHED):
			print('## SCHED.NOW.CHECK    ', didxs)

				## plus anything delayed to now, IF they
				## may be delivered in this window

		debugmsg(f'## T.START0.COUNT={ len(didxs) }', 1,
		         type=vTRC_SCHED)
		if ds:
			debugmsg('## T.DELVS.NOW=' +
				f'{ ",".join(str(di)  for di in didxs) }', 1)

				## time assignments in current round
				## nr. of possible pairs (total)
				## does this combination break/backtrack?
		curr, pairs, btrack = {}, 0, False
				##
				## curr {
				##	delivery: [[veh.ID, ASAP], ...]
				## }
				## collects only already running vehicles
				## new vehicle assignments or delays handled
				## differently
				##
				## pairs is total nr. of non-special
				## vehicle assignments
				##
		spec_sched = {} ## number of special schedule options,
				## indexed by delivery index

				## delivery indexes which may be delayed
				## or may be assigned a new vehicle,
				## respectively
		may_delay, may_assign_new = {}, {}
				##
				## note: redundant; consolidate, see
				## vDELAY_DELIVERY and vNEW_VEHICLE

		ds = list(sorted(ds, key=del_unit2sort))
		for d in ds:
			didx     = d[ 'index' ]
			x, y     = d['x'], d['y']
			new_load = [ d['primary'], d['secondary'] ]
			                 ## assigning new vehicle or delaying

			debugmsg(f'## T.DELV.IDX={ didx }', 1)
			debugmsg(f'## T.DELV.WINDOW={ d["time"] }', 1)
			debugmsg(f'## T.DELV.XY={ x },{ y }', 2,
			         type=vTRC_MAP)

			spec_sched[ didx ] = 0

			vs   = vehicle_may_reach(x, y, t, vpos, xy2d, d,
			                         assign_new=False)
			vids = vehicles_which_may_deliver(new_load, vs,
			                                  vpos, minute0=t0)
			curr[ didx ] = vids
			if (avail > 0):
				may_assign_new[ didx ] = 1
				spec_sched[ didx ] += 1

			if has_time_after(d, t):
				may_delay[ didx ] = 1
				spec_sched[ didx ] += 1
				curr[ didx ].append([ vDELAY_DELIVERY, t0, ])

				## categorize all possibilities; pick option
				## to descend into.  split option tuples into
				## (1) assigned (2) alternate groups; first
				## one is assigned, second one will be picked
				## up when backtracking
				##
				## each delivery has only one option assigned
				## to it; if out of options, backtrack.

			if (vids == []) and (spec_sched[didx] == 0):
				btrack = True
				break

			pairs += len(curr[ didx ]) + spec_sched[didx]

		if btrack:
			assert(0)
			pass

		if debug_is_active(1, vTRC_SCHED):
			print('## DELV.SCHED.TUPLES[time.w=' +
				f'{ tunit }].COUNT={ pairs }')
			print(f'## VEH.AVAIL={ avail }')

			for d in sorted(curr.keys()):
				dstr = ",".join(delvtuple2str(v, asap)
				                for v, asap in curr[d])
					##
				print(f'## DELV[{ d }]={ dstr }')

		if curr == {}:     ## no delivery to schedule in this time unit
			backtrack.append([])
			btrack_alt.append([])
			continue
				## already backtracked above w/o valid schedule

					##------------------------------------
					## nr. of options for each delivery
					## incl. delay or new vehicles
		nro = {}
		for d in curr.keys():
			nro[d] =  len(curr[d]) + (1 if (d in may_delay) else 0)
			nro[d] += (1  if (d in may_assign_new)  else 0)

		assert(0 < min(nro.values()))
					##
					## if delivery exists with no options,
					## MUST have already backtracked above

		##----------------------------------------------------
		## split [delivery: vehicle, ASAP] tuples' list
		## to 'taken', 'not taken' list of options
		##
		## one option per delivery; rest go to
		## alternates for backtrack-alternate stack


		##====================================================
		## this is where choice-enumeration magic happens
		##
		## collect all additions to 'now' and 'alt', then append
		## to backtrack[]/btrack_alt[]
		## entries are [ d.index, vehicle ID, ASAP, ]
		##
		## we do not currently organize that way, but this two-step
		## build would allow context-aware sorting of
		## currently-selected assignments
		##
		now, alt = [], []

				## (1) index of deliveries with only one option,
				##     excluding new vehicles (which are
				##     capacity-limited, and counted below)
				## assign these unconditionally
				##
		didxs_1choice = list(sorted(di  for di in curr.keys()
		                     if ((nro[di] == 1) and
		                         (not di in may_assign_new))))

		if didxs_1choice and debug_is_active(2, vTRC_SCHED):
			print('## DELV.FIXED=', didxs_1choice)
							## TODO: pretty-print

		for di in didxs_1choice:
			if di in may_delay:
				now.extend([ di, vDELAY_DELIVERY, minute0, ])
			else:
				now.extend([ di, curr[di][0][0],
				             curr[di][0][1], ])

				## (2) trim current-index list to anything
				##     remaining with multiple choices
				##
		didxs = list(di  for di in didxs  if (not di in didxs_1choice))

				## (3) enumerate delivery-vehicle assignments
				##     considers number of available ones
				##
		vas = list(vehicle_assignments(didxs, curr, t0, avail,
		                               may_delay))

				## are there enough unassigned vehicles
				## to try all the single-option ones?
				##
				## if not, we need to backtrack: previous
				## choices do not leave us enough unassigned
				## vehicles which SHOULD be assigned now

				## (3) choices (tuples) for each
				##     still-unassigned delivery
				##
				## TODO: 'allow new vehicle' strategy
		for di in didxs:
			v, asap = curr[di].pop(0)

#			if (di in may_assign_new):
#				avail -= 1

			now.append([ di, v, asap, ])
#			if (v == vDELAY_DELIVERY):
#				maydelay[di] = 1

			for v, asap in curr[di]:
				alt.append([ di, v, asap, ])

			continue   ## XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

			vchoices = list([v, asap]  for v,asap in curr[di]
			                if not is_special_vehicle(v))
				##
				## choices which involve actual vehicles
				##
				## try them in increasing distance order,
				## which SHOULD be the case by now
				## (after vehicle_may_reach())

				## no newly assigned vehicle would
				## arrive later than an existing one,
				## since we assume the former will be
				## started early enough to hit the
				## start of current time unit.
				##
				## note: a vehicle MAY also arrive
				## immediately, f.ex. if its earliest
				## arrival would have been in a preceding
				## time unit, when this delivery would not
				## have been possible.

			while True:         ## first suitable case breaks
				newv = []
				if di in may_assign_new:
					newv = [ di, vNEW_VEHICLE,
					         timevec2asap(t, minutes=True),
					]

				if asap:
					if newv:
						now.append(newv)

					elif vchoices:
						va = vchoices.pop(0)
						now.append([ di, va[0], va[1], ])

					if vchoices:
						alt.extend([ di, v, asap, ]
						       for v,asap in vchoices)
					break

				if alap:
					vchoices = list(reversed(vchoices,
				                key=operator.itemgetter(2)))
					##
					## prefer later-to-earlier deliveries
					## input list was chronological

## TODO: recurring primitive, factor out
## (will be simplified once this is simplified to a Karnaugh map)

					if vchoices:
						va = vchoices.pop(0)
						now.append([ di, va[0], va[1], ])
						alt.extend([ di, v, asap, ]
						       for v,asap in vchoices)
					break

				if newv:
					now.append(newv)

				if vchoices:
					va = vchoices.pop(0)
					now.append([ di, va[0], va[1], ])
					alt.extend([ di, v, asap, ]
					           for v,asap in vchoices)

				break
			##-----  end of assign-one-delivery loop

		newvhs = list(di  for di in didxs_1choice
		              if (v == vNEW_VEHICLE))
				##
		newvhs.extend(di  for di,v,asap in now  if (v == vNEW_VEHICLE))

		##-----  now[] 

					## ASAP/ALAP? clear preference for 
					## immediate assignment or delay

		##=====  end of choice-enumeration magic  ====================

		backtrack.append(now)
		btrack_alt.append(alt)

		debugmsg('##', 1)
		continue

		ds = list(d  for d in dels
		          if ((t & d['time2vec']) and
		              (not is_delivery_frozen(d))))
				##
				## deliveries (1) not yet scheduled
				## (2) can be delivered in this window

				## build (delivery, vehicle) pairs, listing
				## all vehicles which may hit this delivery
				##
				## - all specific, already traversing vehicles
				##   which may reach this delivery (in the
				##   currently checked window)
				##
				## - available but not yet started vehicles
				##   are assigned from a 'pool' as they
				##   are interchangeable. we only need to
				##   keep track of how many there are,
				##   and one is sufficient to 'assign'
				##   (since we do not care about which one)
				##
				## - an extra 'virtual vehicle' is added
				##   if delivery may be delayed. this is
				##   a placeholder, making it explicit that
				##   the delivery has been considered, but
				##   it does not happen now.
				##
				## - conversely, if delivery may not be
				##   delayed, is not reachable, and we are
				##   out of unassigned vehicles,
				##   we must backtrack.

		ds = list(sorted(ds, key=del_unit2sort))
		for d in ds:
			didx = d[ "index" ]

			debugmsg(f'## T.DELV.IDX={ didx }', 1)
			debugmsg(f'## T.DELV.WINDOW={ d["time"] }', 1)

			x, y = d['x'], d['y']
			new_load = [ d['primary'], d['secondary'] ]

			vs   = vehicle_may_reach(x, y, t, vpos, xy2d, d)
			vids = vehicles_which_may_deliver(new_load, vs, vpos)

			curr[ didx ] = vids

			if has_time_after(d, t) and (not asap):
				curr[ didx ].append([ vDELAY_DELIVERY, 0, ])

			if vids == []:
				if has_time_after(d, t):
					backtrack.append(
						btrack_delivery(d, delay=True) )
					print(f'## DELAY[{ didx }]')
					continue
				vids = [ vDELAY_DELIVERY, ]

				raise ValueError("no suitable delivery")
							## backtrack

			backtrack.append( btrack_delivery(d) )

				## descend into all (this.delivery, vehicle)
				## options

			debugmsg(f'## D.DELV.V[{didx}]=' +
			         f'{ ",".join(v[0] for v in vids) }', 2)
			debugmsg(f'## D.DELV.V.ASAP[{didx}]=' +
			         ",".join(f"{v[1]}" for v in vids), 2)

			continue

			if len(vids) > 1:
				pass

			for vid, asap in vids:
				backtrack.append(
					btrack_vehicle(vpos[vid], vid, d))

				debugmsg(f'## V.ASSIGN[{ didx }]=[{ vid }]', 2)

				upd = vehicle2xy(vpos, vid, asap, d,
				                 update=True)
				d[ 'minutes' ] = asap

			if debug_is_active(2):
				list_backtrack(backtrack)

		debugmsg('##', 1)

##			if vids == []:
##				if has_time_after(d, t):
##					backtrack.append(
##						btrack_delivery(d, delay=True) )
##					print(f'## DELAY[{ didx }]')
##					continue
##				vids = [ vDELAY_DELIVERY, 0, ]
##
##				raise ValueError("no suitable delivery")
##
##			for vid, asap in vids:
##				backtrack.append(
##					btrack_vehicle(vpos[vid], vid, d))
##
##				debugmsg(f'## V.ASSIGN[{ didx }]=[{ vid }]', 2)
##
##				upd = vehicle2xy(vpos, vid, asap, d,
##				                 update=True)
##				d[ 'minutes' ] = asap
##
##			backtrack.append( btrack_delivery(d) )
##
##				## descend into all (this.delivery, vehicle)
##				## options
##
##			debugmsg(f'## D.DELV.V[{didx}]=' +
##			         f'{ ",".join(v[0] for v in vids) }', 2)
##			debugmsg(f'## D.DELV.V.ASAP[{didx}]=' +
##			         ",".join(f"{v[1]}" for v in vids), 2)

	tend = time.perf_counter()
	debugmsg(f'## time(PACK.ROUTE.ASSIGN0)={ timediff_str(tstart, tend) }',
	         lvl=2, type=vTRC_TIME)
	tstart = tend
	##-----  tstart is after initial greedy assignment  ------------------

	vpos = vpos0

	##-----  v3:  --------------------------------------------------------

	dlist = copy.deepcopy(aux)

				## all entries, replicated from aux
				## sorted in increasing urgency order
				##
## key=del_timesort -> increasing urgency
##	dlist = sorted((copy.deepcopy(a) for a in aux), key=del_timesort)

	dlist = list(sorted(list(dlist), key=del_unit2sort))

	for d in dlist:
		idx = d[ 'index' ]
		if not 'start' in d:
			continue

##		tvec, x, y = d['time2vec'], d['x'], d['y']
		tvec, x, y = d['start'], d['x'], d['y']
		if tvec == 0:
			continue

		assert('start' in d)       ## must have initial-assigned by now

		print(f"##   DELIVERY={ len(place) +1 }/{ len(dlist) }")
		print(f"## T={ d['time'] }  [t.vec=x{ tvec :0x}]")
		print(f"##   START={ d['start'] }u")
		print("##   TW=" +timevec2utilstr(tvec, maxu, sep='',
		                                  unitcols=1))

		vs = vehicle_may_reach(x, y, tvec, vpos, xy2d, d)
		if vs == []:
			raise ValueError("no suitable delivery")

		primary, secondary = d['primary'], d['secondary']
		vid_picked, arrival = None, vTIME_UNDEF

## RRR
		for v in vs:
			vid = v[0]
			v1  = vehicle2primary  (vpos[ vid ])
			v2  = vehicle2secondary(vpos[ vid ])

			if (primary +v1) > MAX1:
				print(f"##   OVERLOAD[{ vid }]: " +
				      f"{ primary + v1 }")
				continue

			if MAX2 and ((secondary +v2) > MAX2):
				print(f"##   OVERLOAD.SECONDARY[{ vid }]: " +
				      f"{ secondary + v2 }")
				continue

			if (vid_picked == None) or (v[2] < arrival):
				vid_picked, arrival = vid, v[2]
## RRR

		if vid_picked == None:
			raise ValueError("no suitable vehicle")

		print("##  del=" +timevec2utilstr(minute2timevec(arrival),
		                                  maxu, sep='', unitcols=1))
				##
		print(f'## DEL { vid_picked } at { minute2wall(arrival) }')
		print(f'## ADD { vid_picked } {primary} sec={secondary}')
		vehicle2xy(vpos, vid_picked, arrival, d)
		print('')
		place.append([ vs[0], [], ])
				## TODO: remember alternatives


##					## filter vehicles which may reach
##					## the suitable deliverxy2dist windows
##		vs = vehicle_may_reach(x, y, tvec, vpos, xy2dist)
##		if vs == []:
##			raise ValueError("no suitable delivery")
##					## -> backtrack
##
##		primary, secondary = d['primary'], d['secondary']
##		vid_picked, arrival = None, vTIME_UNDEF
##
##		for v in vs:
##			vid = v[0]
##			v1  = vehicle2primary  (vpos[ vid ])
##			v2  = vehicle2secondary(vpos[ vid ])
##
##			if (primary +v1) > MAX1:
##				print(f"##   OVERLOAD[{ vid }]: " +
##				      f"{ primary + v1 }")
##				continue
##
##			if MAX2 and ((secondary +v2) > MAX2):
##				print(f"##   OVERLOAD.SECONDARY[{ vid }]: " +
##				      f"{ secondary + v2 }")
##				continue
##
##			if (vid_picked == None) or (v[2] < arrival):
##				vid_picked, arrival = vid, v[2]
##
##		if vid_picked == None:
##			raise ValueError("no suitable vehicle")
##
##		print("##  del=" +timevec2utilstr(minute2timevec(arrival),
##		                                  maxu, sep='', unitcols=1))
##		print(f'## DEL { vid_picked } at { arrival }')
##		print(f'## ADD { vid_picked } {primary} sec={secondary}')
##		vehicle2xy(vpos, vid_picked, arrival, d)
##		print('')
##		place.append([ vs[0], [], ])
##				## TODO: remember alternatives

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

	elif random.randint(0, 100) < 50:               ## 1 in 20: two windows
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
## typical .mkv sizes, bimodal distribution with two normal peaks
##
def random_weight():
	mn, expd, var = 100, 750, 100
	mega = 1000000

	if random.randint(1, 100) <= 25:          ## small files
		mn, expd, var = 50, 200, 75

	return int(max(mn * mega, random.gauss(expd * mega, var * mega)))


##--------------------------------------
## generate [approximate] distance-to-cost lookup from X,Y pairs in
## extended-format input
##
## JSON output:
## {
##   'points': [[X0, Y0], [X1, Y1], ...],
##   'time':   [[0.0, dist(XY0->XY1), dist(XY0->XY2)... ],
##              [dist(XY1->XY0), 0.0, dist(XY1->XY2)... ],
##   ]
## }
##
## note: currently, only symmetric costs (symm. approximations only)
##
def xy2table(tab, aux, fmt='json'):
	pts  = list((p['x'], p['y'])  for p in aux)
	cost = []

	for si, src in enumerate(pts):
		cost.append([])

		for di, dst in enumerate(pts):
			if (si == di):
				dist = 0.0
			else:
				dist = xy2time(src[0], src[1], dst[0], dst[1])
			cost[-1].append(dist)

	res = {
		'points': pts,
		'time':   cost,
	}
	if fmt == 'json':
		print(json.dumps(res))
	else:
		print(xy2c(res, pts))

	return 0


##--------------------------------------
##
def random_xy(border):
	while True:
		x = random.randint(0, 1<<64)
		y = random.randint(0, 1<<64)
		x /= (1 << 64)
		y /= (1 << 64)

		if not pathtools.is_inside(x, y, border):
			continue
		break

	return x, y


##--------------------------------------
## call only with RNTIME set
## adds random, in-polygon points if 'RNCOORDS' is set
##
## generates new delivery points if 'RNITEMS' is set
##   - basic format, N elems, if 'RNCOORDS' is not set
##   - extended format, with X,Y coordinates within polygon if RNCOORDS is set
##
## TODO: centralized polygon reading, pass through 'border',
##       do not read RNCOORDS directly
##
def table_partial2full(t, border=None):
	if ('RNTIME' in os.environ) and (not 'SEED0' in os.environ):
		seed = os.environ[ 'RNTIME' ]
		if len(seed) >= 2:
			random.seed( seed.encode('utf-8') )

	if t != None:
		deliveries = list(delivery_times() for _ in t)
	else:
		t = []
	border, coords = None, []

	if 'RNCOORDS' in os.environ:
		border = (t.decode().split() for t in
		         open(os.environ['RNCOORDS'], 'rb').read().split(b'\n'))
			##
		border = list([float(t[0]), float(t[1])]
		              for t in border  if (len(t) == 2))
			##
			## X+Y segments, preserving order

		brd, prevx, prevy = [], border[0][0], border[0][1]
## TODO: centralize and name
## see reference from xytable()
##
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

	##--------------------------------------------------------------------
	if 'RNITEMS' in os.environ:
		n = int(os.environ['RNITEMS'])
		res = []

		nd = math.ceil(math.log10(n))

		for i in range(n):
			wgt = random_weight()

			if 'RNCOORDS' in os.environ:
				x, y = random_xy(border)
				t    = times2print( delivery_times() )
				val  = [ wgt, 1, f"{x:.06}", f"{y:.06}",
				         t,
				         f"unit{ len(res) :>0{nd}}", ]

			else:
				val = [ wgt, 1, f"UNIT{ len(res) }", ]

			res.append(','.join(str(v) for v in val))

		for r in res:
			print(r)

		return 0

	##--------------------------------------------------------------------
	if 'RNCOORDS' in os.environ:
			## generate delivery points, within polygon
		while len(coords) < len(t):
			x, y = random_xy(border)
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

	if 'SEED0' in os.environ:
		seed = os.environ[ 'SEED0' ]
		random.seed( seed.encode('utf-8') )

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

	if (not 'RNTIME' in os.environ):
		if (not 'MAX1' in os.environ):
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

	bases, xy2dist_table = None, None
	if ('BASE' in os.environ):
		bases = str2bases(os.environ[ 'BASE' ])
		if not bases:
			terminate("invalid list of bases (" +
			          f"{ os.environ[ 'BASE' ] })")

	if ('DIST' in os.environ):
		distf = os.environ[ 'DIST' ]
		xy2dist_table = json2distances(distf)
		if not xy2dist_table:
			terminate("can not read XY-to-distance DB ({distf})")

	vehicles = [None] * env2num('VEHICLES', 1)

##---  /parameter-read code

	sys.argv.pop(0)
	if not 'RNTIME' in os.environ:
		if [] == sys.argv:
			usage()
		tbl, aux = table_read(sys.argv[0], 2  if FIELD2  else 1,
		                      fmt='base')
	else:
		tbl = None

	if (('RNTIME' in os.environ) or ('RNCOORDS' in os.environ) or
	    ('RNITEMS' in os.environ)):
		sys.exit( table_partial2full(tbl) )

	if ('XY2TABLE' in os.environ):
		fmt = 'C'  if ('TO_C' in os.environ)  else 'json'
				##
		sys.exit( xy2table(tbl, aux, fmt=fmt) )

	if bases and aux:
				## TODO: hardwared vehicle/shift plans
				## at least one vehicle with multiple windows
		v = {
			'V0': {			## refill windows for V0:
				'1100-1200+1300-1400',
				'1600-1700',
			},

			'V1': [
				'1300-1500',
				'1700-1830',
			],

			'V2': [
				'1300-1415',
				'1730-1900',
				'0945-1030',
			],

			'V3': [
				'1400-1515',
			],

			'V4': [
				'1400-1515',
			],

			'V5': [
				'1400-1515',
			],

			'V6': [
				'1400-1515',
			],

			'V7': [
				'1400-1515',
			],
		}

		for sched in pack_and_route(tbl, aux, bases, vehicles,
		                            vrefill=v, xy2d=xy2dist_table):
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

