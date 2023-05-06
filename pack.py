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
##                    time   execution time
##                    map    coordinates, paths, other mapping-related items
##                    sched  any schedule-related parameter
##                    pack   details of bin packing
##                    stack  details of backtracking
##                    flow   control/data flow
##                    all    any traceable quantity (all of the above)
##   SAT=...            output SAT solver input for the current problem
##   SATDEBUG=...       diagnostics level if >0, SAT-only diagnostics
##   SAT_VEHICLES=...   number of vehicles to assume, over BFD-derived limit
##                      absolute number, or +...relative to BFD-limit...
##
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
##   NOTE: setting PACK_N_ROUTE_SKIP in env falls back to SAT solver
##
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
import textwrap


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

sSATPREFIX  = 'SAT='      ## common prefix for data applicable to SAT solvers
sSATCOMMENT = '## SAT='   ## SAT-related comment, for our own tracing
sSAT_CONSTR_END = ' 0'    ## terminate [term list of] constraint
sSAT_2ND_VAR    = 'NV'    ## prefix for secondary SAT (CNF) variables
sSAT_SYM_PREFIX = 'RAW='  ## prefix for clauses which are stored as strings,
                          ## only mapped to integer indexes in the end
                          ## DIMACS CNF: "1 2 -3 0"
                          ## 'raw' CNF:  "D1 D2 -D3"


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

## early-terminating search timeout, in milliseconds
vTIMEOUT_MSEC = 3000.0


##----------------------------------------------------------
## BFD-scan parameters
##
## how many units of immediate future to consider, when checking for
## next-available candidates
vNEXTUNITS = 4
##
## see also vTIME_UNIT_MINS
##
## do not consider more than this many candidates at each
## position, when BFD-searching for candidates
vBFD_MAX_CANDITATES = 3


##----------------------------------------------------------
## trace types (bitmask)
vTRC_TIME  =    1
vTRC_MAP   =    2     ## map-related properties: coordinates, distances
vTRC_SCHED =    4     ## schedule-related properties: options when
                      ## assigning units to dispatch etc.
vTRC_STACK =    8     ## details of backtrace stack
vTRC_PACK  = 0x10     ## details of packing
vTRC_FLOW  = 0x20     ## control/data flow

## not a real switch: used when (debuglevel >= X) AND tracing bits are needed
vTRC__AND  = 0x8000000000000000


##----------------------------------------------------------

TARGET = None        ## set to [ host, port ] if env specifies it

CRLF   = b'\n\r'     ## telnet official separator
COMM   = b'#'        ## prefix for commented log results

vTIME_UNIT_MINS = 15   ## how many minutes are in one time-vector unit
vTIME_UNDEF = int(9E9) ## value for time vector meaning 'undefined' (=too high)
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
	sys.stdout.flush()                          ## clear any preceding text
	sys.stderr.write(msg +'\n')
	sys.stderr.flush()
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
	'pack':  vTRC_PACK,
	'stack': vTRC_STACK,
	'flow':  vTRC_FLOW,

	'all':   vTRC_TIME | vTRC_MAP | vTRC_SCHED | vTRC_PACK | \
			vTRC_STACK | vTRC_FLOW,
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
## TODO: SAT-solver specific wrapper


##--------------------------------------
## returns False to allow set-log-passthrough chains
##
## 'type' is bitmask of vTRC... types, if specific event
## if any of these are enabled by 'TRACE', message is output
## regardless of debug level
##
def debugmsg(msg, lvl=1, type=0):
	if (type & vTRC__AND):
		type &= ~vTRC__AND;

		if (((type & tracetypes) == 0) or (not debug_is_active(lvl))):
			return False

	elif debug_is_active(lvl) or (type & tracetypes()):
		print(msg)

	return False


##--------------------------------------
def timediff_msec(tstart, tend):
	return 1000.0 * (tend - tstart)


##--------------------------------------
## transform to human-scaled time
## start, end must have been supplied by time.perf_counter()
##
def timediff_str(tstart, tend):
	ms   = timediff_msec(tstart, tend)
	unit = 'ms'

	return(f"{ ms :.2f}{unit}")


##--------------------------------------
## measures and formats current time, relative to 'tstart',
## as delta(time)
##
## returns current time to allow chaining calls, possible to assign
## to 'next ref. start time'
##
## 'tstart' must have been set by previous perf-counter read
##
def timediff_log_now(tstart, descr):
	curr = time.perf_counter()

	debugmsg(f'## time({ descr })={ timediff_str(tstart, curr) }',
	         lvl=2, type=vTRC_TIME)

	return curr


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
				'traversal cost (minutes)',
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
## returns 'defval' if key is not present in dict
## defaultdict() inl
##
def dict2val(d, key, defval=None):
	return  d[key]  if (key in d)  else defval
##
## TODO: deduplicate (if there is an alternative)
## TODO: use for preexisting 'check-for-default' conditional expressions


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
					## TODO: deal with optional deliveries
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
##     'vehicle_may': bitmask of vehicles which may be assigned
##                    -1 if any vehicle may deliver (which would be
##                    understood as default if key is missing)
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

## TODO: centralized return-all0 for struct

			aux.append({
				'primary':     fd1,
				'secondary':   fd2,
				'time':        f[4],         ## original string
				'time2vec':    t,
				'time_units':  pathtools.bitcount(t),
				'index':       fi,
				'min_time':    mint,
				'max_time':    maxt,
				'vehicle_may': -1,
				'x':           x,
				'y':           y,
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
## 'skip_as_input' is (... in X)-capable list/dictionary, of non-None
## elements listed there are ignored in 'tbl'
##
## check for early termination with max.elems
## since BFD only looks at largest entries, if we hit the limit here,
## that is our achievable optimum
##
## see also: best_fit_decreasing_multiple(), a wrapper around this
##
def best_fit_decreasing(tbl, max_elems=0, return_sum=False, skip_as_input=None):
	sel, nsel, sum1, sum2, printed = [], [], 0, 0, 0

	for t in tbl:
		ok = True
				## TODO: sanity-check BFD-compatible input
		if len(t) < 4:
			continue

		if skip_as_input and (t[2] in skip_as_input):
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
			print(f"## sum: {sum1} -> {newsum} [" +
				f"left={MAX1-newsum}, " +
				f"{ratio(newsum, MAX1):.2f}%]")
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

	if return_sum:
		return sel, nsel, sum1

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
def xy2minutes(x, y, x0, y0, wgt=1.0, start_minutes=None):
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
	"bitmask: all time units strictly after all max(units(t))"

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

## TODO: bit_length() SHOULD be available everywhere

	return lsb
			## ... & (t-1) removes LS one bit


##--------------------------------------
## "...start-end..." string for [single-bit] time vector
##
def timevec2wall(t):
	start = minute2wall(timevec2asap(t, True))
	end   = minute2wall(timevec2asap(t << 1, True) -1)

	return f"{ start :04}-{ end :04}"
##
## TODO: do we have a centralized wrapper for this?


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
##   see also VRoute Status, which is a struct used during searching
##
## 'V.ID': {
##    'stops':    [ [ minute of arrival, delivery ID, X, Y, ],
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
##    'totaldist':  sum(travel distances)
##
##    'START.X':    X coordinate, start of deliveries
##    'START.Y':    Y coordinate...
##    'START.MINS': 0-based minute
## }


##--------------------------------------
## Delivery Arrival Status
##
## 'delivery ID': {
##     'vehicle': vehicle ID,
##     'minute':  ...arrival time...
## }
## 'VEHICLE2TIME': {              ## which is not a valid (numeric) delivery ID
##                                ## see tVID2TIME as symbolic key
##   'vehicle ID': [
##     {
##       'delivery': delivery ID,
##       'minute':  ...arrival time...
##     }
##   ]
## ]
##
## redundant, to simplify both vehicle-counting and delivery-sorting use
##
## MUST be consistent with 'stops' of delivering vehicles

tVID2TIME = 'VEHICLE2TIME'               ## 



##--------------------------------------
## VRoute Status
##   statistics for delivery orders when searching for minimum
##
## {
##    'primary':    sum of primary fields in already scheduled deliveries
##    'secondary':  ...secondary fields...
##
##    'distances': [ distance1, distance2, ... ]
##                  -- total distance for full sequence of deliveries
##
##    'd_minutes': [ xy travel time1, xy travel time2, ... ]
##                  -- net minutes, without delivery overhead
##    'stops': see V.ID Vehicle Status field
##                  -- nr. of elements in 'd_minutes', 'distances',
##                  -- and 'stops' match
##    'deliveries': { ID of delivery: arrival time }
##                  -- additional detail
##                  -- redundant, same info present in 'stops' array,
##                  -- kept for simplified lookups
##    'arrivals':   [ [ arrival time, delivery ID, ] [ arrival 2, ... ] ]
##                  -- entries are in increasing arrival-time order
## TODO: stops/deliveries/arrivals together are redundant
##       (they evolved from different sub-functions, and converged)
##       when we finalize sorting code, remove the then-unused one
##       note: time-based sorting
##
##    'checked':    -- dictionary of new routes (ID+time strings);
##                  -- appended when new route is being explored
##                  -- TODO: redundant: remove once exploration
##                  -- is completely tracked + protected against recursion
## }
##
## per-search status, not (yet?) landing in global struct -> no V.ID index


##--------------------------------------
## TODO: Python version-portable automatic values
##
def vehicle2primary(vehicle):
	return  vehicle[ 'primary' ]  if ('primary' in vehicle)  else 0


##============================================================================
## unconditionally defined SAT variables (ignore any spaces):
##   dXX tYY         -- delivery XX is scheduled in time unit YY
##   dXX tYY vZZ     -- vZZ is v0..v(N-1) for N-bit vehicle IDs
##                   -- all-0 vehicle ID means no vehicle assigned
##       -> dXX tYY  true if and only if at least one of 'dXX tYY vZZ' is 1
##       -> MUST check for dXXtYYv0..dXXtYYv(N-1) not encoding an index
##          over limit. (<=M with M vehicles is fine; effective encoding
##          is one-based, with 0 indicating absence.)
##
## conditionally defined variables:
##   A nand B    -- NAND(A, B); used to check for either dXX tYY or dWW tZZ
##                  are all-0 (-> not yet assigned to vehicle)
##                  -- defined for all potentially conflicting dXX tYY, dWW tZZ
##                  -- delivery+unit pairs
##   A xor B  -- XOR(..., ...): the two variables differ
##                  -- defined for all potentially conflicting
##                  -- delivery+time+vehicleID(bit) assignments ->
##
## unconditional constraints:
##   - exactly one of 'dXX tYY' is 1 for every delivery dXX:
##     (1) delivery is scheduled sometime
##     (2) it is scheduled exactly once
##       - TODO: will not be true once we allow delaying a delivery (which
##         may not be assigned in the current time horizont) -> one-of-N
##         assignment for those will be conditional
##     (3) side note: gives an immediate ordering for vehicle tYY, since
##         it assigns deliveries+units in delivery order. (at current
##         settings, units are sufficiently granular that not more than
##         one delivery may be scheduled to them. this might change with
##         multi-delivery batches, which we do not currently support.)
##
## design decisions:
##   - one-hot encoding of vehicle IDs would be counterproductive. less
##     variables and more bitwise comparisons appear to
##     be solver-friendlier.
##
## DO NOT CHANGE THESE CONVENTIONS UNLESS YOU KNOW WHAT YOU ARE DOING
##
## see satsolv_var_name() which encapsulates delivery+time -> SAT name mapping


##--------------------------------------
## SAT-solver aux. data
## all variables are Booleans
##
## {
##    'delv_units': { ... }
##                -- delivery+time windows' variables:
##                -- dXX_tYY: delivery XX may be delivered in time unit YY
##                -- see also below
##
##    'delv_veh_units': { ... }
##                -- delivery+time+vehicle assignment variables:
##                -- dXX_tYYvZZ: delivery XX is delivered in time unit YY
##                -- by vehicle ZZ
##
##    'vars':     [ ...list of variables in order of addition... ]
##
##    'added_vars':   -- extra variables introduced by CNF constructions
##
##    'constraints':   [ [ ...text of constraint1..., ...comment... ] ]
##                -- CNF clauses (each is an OR of variables)
##                --
##                -- whitespace-separated list of variables, possibly
##                -- with leading '-' indicating negation ("A -B CMD")
##                --
##                -- empty constraints are possible; they are used by
##                -- comment-only additions f.ex.
## }
##
## struct stores arbitrary values for 'delv_units' etc.; only their keys matter


## SAT-solver format specification:
##
## DIMACS format (simplified version):
##     Jaervisalo, Le Berre, Roussel: Rules of the 2011 SAT competition
##     www.satcompetition.org/2011/rules.pdf, section 4.1
## accessed 2023-02-27
## SHA1()=xb08ad0aca66821ee85fb8e05650340f6180db386
## SHA256()=xcab5a36e6dda3efef32be201838012d03a901c04ef3556762442b5010aaeb479
##
## summary:
##     | p cnf ...nr-of-variables... ...nr-of-clauses...
##     |                        -- CNF (conjunctive normal form) only,
##     |                        -- AND-of-OR terms
##     | c ...comment...        -- optional
##     | 1 -2 3 0               -- 1: True, -2: False, 0: end of clause
##     | ...
##
## certain solvers report errors if unreferenced variables/clauses exist.


##--------------------------------------
def use_satsolver():
	return ('SAT' in os.environ)


##--------------------------------------
def satsolv_is_debug(level=1):
	if not ('SATDEBUG' in os.environ):
		return False

## TODO: evaluate int, cache, return

	return True


##--------------------------------------
## number of vehicles to consider
##
def satsolv_vehicle_count(bfd_limit=0):
	if not "SAT_VEHICLES" in os.environ:
		return bfd_limit

	addl, sv = False, os.environ[ "SAT_VEHICLES" ]
	if sv[ :1 ] == '+':
		addl, sv = True, sv[ 1: ]

	sv2 = int(sv, 0)
	if (sv2 < 0):
		raise ValueError(f"invalid delta/vehicle-count ({sv})")

	sv2 += (bfd_limit  if addl  else 0)
	if (sv2 < bfd_limit):
		raise ValueError(f"delta/vehicle-count low ({sv}/{bfd_limit})")

	return sv2


##--------------------------------------
def satsolve_vidx_bits(vehicles):
	"number of bits to encode vehicles in SAT solver, incl. 'no vehicle'"

				## includes pattern to indicate 'not serviced'

	return (vehicles +1).bit_length()


##--------------------------------------
## empty construct for SAT solver aux. data
##
def satsolv_init0():
	return {
		'delv_units':     {},
		'delv_veh_units': {},
		'vars':           [],
		'added_vars':      0,
		'constraints':    [],
	}


##--------------------------------------
## register key+value to sat{}
## returns False if value has already been set, True if has just been added
##
def satsolv_add1(sat, key, value):
	rv = True
	if sat:
		assert(key in sat)
		rv = not ('value' in sat[ key ])
		sat[ key ][ value ] = 1

	return rv


##--------------------------------------
## with 'time_unit' None, returns delivery+v0...v(N-1) bits, which
##                        describe which vehicle this delivery is assigned to
##
##      'vnumber'   None, returns only delivery+time main variable
##
def satsolv_var_name(delv_id, time_unit=None, vnumber=None):
	if (time_unit == None) and (vnumber == None):
		raise ValueError("no delivery-only variable names supported")

	tunit_id = f"t{ time_unit }"  if (time_unit != None)  else ''

	if vnumber != None:
		return f'd{ delv_id }{ tunit_id }v{ vnumber }'

	return f'd{ delv_id }{ tunit_id }'


##--------------------------------------
## returns variable ID for this delivery+unit
##
def satsolv_add_delvtime(sat, delvid, unit, vnumber=None):
	var = satsolv_var_name(delvid, time_unit=unit, vnumber=vnumber)
	add = False

	if vnumber != None:
		add = satsolv_add1(sat, 'delv_veh_units', var)
	else:
		add = satsolv_add1(sat, 'delv_units', var)

	if add:
		assert(var not in sat[ 'vars' ])
		sat[ 'vars' ].append(var)

	return var


##--------------------------------------
def satsolv_add_1var(sat, var):
	if sat and (not var in sat[ 'vars' ]):
		sat[ 'vars' ].append(var)


##--------------------------------------
## register 'vars' as new variables
##
## bundle as many as possible
## esp. delivery+time-unit collisions add many short lists -> O(N^2) extension
##
## intermediate set: "not in sat['vars']" is slow re-search
##
def satsolv_add_vars(sat, vars):
	if sat:
		seen = set(sat['vars'])
		v = (v  for v in vars  if (not v in seen))
		sat[ 'vars' ].extend(v)


##--------------------------------------
## not checking for replication
##
def satsolv_add_constraint(sat, vars, comment=''):
	if sat and ('constraints' in sat):
		sat[ 'constraints' ].append([ " ".join(vars), comment ])


##--------------------------------------
def satsolv_add_comment(sat, comment):
	if sat and ('constraints' in sat):
		sat[ 'constraints' ].append([ '', comment ])


##--------------------------------------
## register 'raw', preformatted constraint
## not checking for replication
##
def satsolv_add_constraint1(sat, rawc, comment=''):
	if sat:
		sat[ 'constraints' ].append([ rawc, comment ])


##--------------------------------------
## handed a list of [ delivery ID1, time unit1, delv.ID2, time unit2 ] tuples,
## plus 'veh_count' as nr. of vehicle-ID indexes
##
## register 'at least one vehicle-ID set is all-0 (unassigned) OR ID1 != ID2'
## clauses
##
## sat[ "vars" ] MUST already have initalized all referenced dXXtYY etc.
## variables.
##
def satsolv_add_conflict_constraints(sat, constr, veh_count):
	d1, t1, d2, t2 = constr

	vbits  = satsolve_vidx_bits(veh_count)
#	v1main = satsolv_var_name(d1, time_unit=t1)
#	v2main = satsolv_var_name(d2, time_unit=t2)
#	v12nand, nvar, ncomm = satsolv_nand1(v1main, v2main)
#							## v1main NAND v2main
#	for c in v12nand:
#		satsolv_add_constraint1(sat, sSAT_SYM_PREFIX + c, ncomm)
#		ncomm = ''
#
#	addvars = [ v1main, v2main, nvar ]

	v1bits = list(satsolv_var_name(d1, time_unit=t1, vnumber=v)
	              for v in range(vbits))
	v2bits = list(satsolv_var_name(d2, time_unit=t2, vnumber=v)
	              for v in range(vbits))

	cls, neq, comm = satsolv_neq_or0(sat, v1bits, v2bits)
	for c in cls:
		satsolv_add_constraint1(sat, sSAT_SYM_PREFIX +c, comm)
		comm = ''
##
##							## pairwise XORs
##	for v in range(vbits):
##		v1bit = satsolv_var_name(d1, time_unit=t1, vnumber=v)
##		v2bit = satsolv_var_name(d2, time_unit=t2, vnumber=v)
##		xconstr, xn, xcomm = satsolv_xor1(v1bit, v2bit)
##
##		for c in xconstr:
##			satsolv_add_constraint1(sat, sSAT_SYM_PREFIX +c, ncomm)
##			xcomm = ''
##
##		addvars.extend([ v1bit, v2bit, xn ])
##
####
##				## vehicle-encoding variables MUST differ, or
##				## at least one MUST be all-0 for
##				## conflicting (delivery, time.unit) pairs
##				##
##	return addvars


##--------------------------------------
## register 'raw', preformatted comment
##
def satsolv_add_comment(sat, comment):
	if sat:
		sat[ 'constraints' ].append([ '', comment ])


##--------------------------------------
## filter out comment-only constraints, which do not lead to clauses
## comment-only conditions are empty strings for non-comment part
##
def sat_nr_of_clauses(sat):
	if (not sat) or (not "constraints" in sat):
		return 0

	nrc = sum(1  if (c[0] != '')  else  0
	          for c in sat["constraints"])

	return nrc


##--------------------------------------
def satsolv_report(sat):
	if not use_satsolver():
		return

	nrclauses = sat_nr_of_clauses(sat)
							## problem sizes
	print(sSATPREFIX + f'p cnf { len(sat[ "vars" ]) } { nrclauses }')

	print(sSATPREFIX +'c')
	print(sSATPREFIX +'c CONSTRAINTS:')
					## do not change CONSTRAINTS framing

	comments = 0
	for commstr in (s  for s in sat[ "constraints" ]  if s[1]):
		if commstr:
			print(sSATPREFIX +'c   ' +commstr[1])
			comments += 1

	vstr = ' '.join(f'{ v }[{ vi+1 }]'
	                for vi, v in enumerate(sat[ "vars" ]))
	print(sSATPREFIX +'c /CONSTRAINTS:')
	print(sSATPREFIX +'c')

					## do not change VARIABLES framing
					## or update dev/sat2back.py too
	print(sSATPREFIX +'c VARIABLES:')
	for v in textwrap.wrap(vstr, width=64):
		print(sSATPREFIX +'c   ' +v)
	print(sSATPREFIX +'c /VARIABLES')
	print(sSATPREFIX + 'c')

					##-----  end of header  --------------

	for ci, c in enumerate(sat[ "constraints" ]):
		cvars, comment = c[0], c[1]

		if cvars.strip() == '':
			continue
					## map expression to int. indexes
					## each entry MUST be present
					##
		if cvars[ : len(sSAT_SYM_PREFIX) ] == sSAT_SYM_PREFIX:
			constr = cvars[ len(sSAT_SYM_PREFIX): ].split()
			constr = " ".join(str(s) for s in
			                  satsolv_vars2ints(sat, constr))

		else:
			constr = " ".join(str(sat[ "vars" ].index(v) +1)
			                  for v in cvars.split())

		print(sSATPREFIX +constr +sSAT_CONSTR_END)

	print()


##============================================================================
## TODO: Python version-portable automatic values
##
def vehicle2secondary(vehicle):
	return  vehicle[ 'secondary' ]  if ('secondary' in vehicle)  else 0


##--------------------------------------
## returns 'allegedly unique' normalized string form summarizing route
##
## non-None 'delv' (delivery ID) and 'arrive' is mixed into route, if both
## are present. (TODO: this 'mixed into' MUST be an append-to-schedule)
##
## 'arrive' is in minutes; 'delv' is delivery ID
##
## since most checks are expected to check route only, they
## are special-cased to skip array creation/append/etc.
##
## not cross-checking for 'delv' present in route, or other consistency
##
## DO NOT EXPECT NORMALIZED FORMAT TO REMAIN STABLE ACROSS VERSIONS
##
def vroute2normalized(vroute, delv=None, arrive=None):
	"normalized description of route (from VRoute)"

	if ((not vroute) or (not 'deliveries' in vroute) or
	    (not 'arrivals' in vroute)):
		return ''

	r = list(f'min={ a[0] }>delv={ a[1] }'  for a in vroute['arrivals'])

	if (arrive != None) and (delv != None):
		r.append(f'min={ arrive }>delv={ delv }')

	return "__".join(r)


##--------------------------------------
## see also ratio()
def pct2str(val, maxv):
	"standarized-formatted percentage (string)"

	if (val > maxv):
		return "100+%"
	elif (val < 0):
		return "<0%"

	return f"{ (100.0 * val) / maxv :.1f}"


##--------------------------------------
## utilization limit to accept as 'good enough'; >= this value is accepted
## and terminates current search
##
## TODO: allow gradual, annealing-like improvement of quality threshold
## as fn. of items to set decreases
##
def current_anneal_limit(delvs_set, delvs_total):
	ratio = 0.6667

	if delvs_set + 25 < delvs_total:
		if delvs_set + 100 < delvs_total:
			ratio = 0.925

		else:
			ratio = 0.75

	debugmsg(f"## BFD.THRESHOLD.RATIO={ ratio * 100.0 :.1f}%",
	         1, type=vTRC_PACK)

	return ratio * MAX1


##--------------------------------------
## route vehicle with ID 'vid' to delivery in 'id', arriving at 'minutes'
##
## returns time of arrival, in minutes
##
## route MUST have been prefiltered to be consistent with current
## position and delivery window
##
## 'vcost'      is current vehicle VRoute Status (already 'vid'-indexed);
##              updated
## 'arrival'    is delivery-to-minute mapping; unassigned entries are NOT
##              present; updated
## 'deliveries' is complete delivery struct; read-only access
##
## arrival MUST NOT contain entry for 'id' yet
##
def vehicle2xy_minimal_min(vcost, arrival, vid, id, arrv_minute, deliveries):

	##-----  sanity checks  ----------------------------------------------
	if len(deliveries) <= id:
		raise ValueError(f"assigning invalid delivery ID ({ id })")

	if id in arrival:
		raise ValueError(f"delivery ID={id} is already assigned")

	##-----  /sanity checks  ---------------------------------------------

	if vcost[ 'stops' ] == []:
		px, py = None, None
	else:
		px, py = vcost[ 'stops' ][-1][2], vcost[ 'stops' ][-1][3]
							## previous x, y

## TODO: assert_vroute_is_sane(), now that it is centralized

	x, y = deliveries[ id ]['x'], deliveries[ id ]['y']

	if px == None:
 		px, py = 0.5, 0.5
## TODO: dummy mid-of-map base coordinate
	else:
		px, py = float(px), float(py)

	dxy  = xy2dist(float(x), float(y), px, py)
	dmin = xy2minutes(float(x), float(y), px, py)

	vcost[ "distances" ].append(dxy)
	vcost[ "d_minutes" ].append(dmin)

	add1 = deliveries[ id ]['primary'  ]
	add2 = deliveries[ id ]['secondary']

	if (add1 +vcost[ "primary" ] > MAX1):
		raise ValueError(f"delivery ID={id} would overload to" +
		                 f"{ add1 +vcost[ 'primary' ]}")
			##
	if (add1 +vcost[ "primary" ] > MAX1):
		raise ValueError(f"delivery ID={id} would secondary-" +
			f"overload to { add1 +vcost[ 'secondary' ]}")

	vcost[ "primary"   ] += add1
	vcost[ "secondary" ] += add2

	debugmsg(f"## ASSIGN.V[VH={vid},DELV={id}]=" +
	         f"{ arrv_minute }min;LOAD={ vcost['primary' ]}" +
	         f"({ pct2str(vcost[ 'primary' ], MAX1) }%)",
	         1, type=vTRC_SCHED)

	debugmsg(f"## ASSIGN.V[VH={vid},DELV={id}]=" +
	         f"X={x},Y={y},T.ARRV={ arrv_minute }min",
	         2, type=vTRC_MAP)

				## driving to delivery X,Y
				## advance time to arrival + handover latency

	if (id in arrival):
		raise ValueError(f"assigning delivery {id} more than once")

	arrival[ id ] = delv_arrival_status(vid, arrv_minute)

	vcost[ "arrivals" ].append([ arrv_minute, id ])

## TODO: struc spec
	vcost[ 'stops' ].append([
		arrv_minute, id, x, y,
	])
	vcost[ 'deliveries' ][ id ] = arrv_minute

	return arrv_minute


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
## TODO: see vehicle2xy_minimal, which is a closely related subset
## merge them, once vehicle tracking structs are finalized
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
	dt = xy2minutes(float(x), float(y), float(x0), float(y0))
			## delta-t

			## arrival did not account for overhead; add here
	dt = round(now + dt + vTIME_DELIVER_MIN)

	wt = minute2timevec(dt)
## TODO: unify minute/unit accounting -> exact limit filter

	if t:
		maxtb = pathtools.bitcount(t)
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
## NOTE: ASAP arrival, excluding any delivery overhead
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
		                   vehicles[v]['stops'][-1][ 0 ], t=timevec)
## TODO: [0] is minutes field; mark properly
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
## not checking for t being single bit
##
## equivalent bit2offset( msbit(t) ) if t is not power-of-two
##
def timevecbit2offset(t):
	"map bit of time2vec bitvectors to 1-based offset/index"

	return t.bit_length()


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
## 'tprev_min' is the last _arrival_ known before this item
## backtracking amounts to rolling back anything > this minute
##
def btrack_vehicle(v, vid, delivery=None, tprev_min=None):
	"data structure to back up vehicle 'before' state (backtrack form)"

	vraw = copy.deepcopy(v)                       ## resolve all references

	res = {
		'type': 'VEHICLE',
		'id':   vid,
		'data': vraw
	}

	if delivery:
		res[ 'orderid' ] = delivery[ 'index' ]

	if tprev_min:
		res[ 't_min' ] = tprev_min

	return res


##--------------------------------------
## raises exception if ...
##   - vehicles MUST reference controlling delivery (if 'orderid' present)
##   - deliveries which lack vehicles MUST be marked as delayed
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
def best_fit_decreasing_multiple(tbl):
				## try BFD plans as an approximation of
				## how many vehicles are needed
	res   = []
	sel   = [ None, ]
	sums  = []
	taken = []

	while sel:
		sel, _, sum1 = best_fit_decreasing(tbl, MAX_ELEMS,
		                        return_sum=True, skip_as_input=taken)
		if sel:
			res.append(sel)
			sums.append(sum1)
			taken.extend(s[2] for s in sel)
				## ^ register now-selected as already taken

	debugmsg(f'## BFD.ALL.COUNT={ len(res) }', lvl=1, type=vTRC_TIME)
	debugmsg(f'## BFD.ALL={ ",".join(str(n) for n in sums) }',
	         lvl=2, type=vTRC_PACK)

## TODO: min-max statistics etc.

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


## ##--------------------------------------
## ## human-readable form for special assignments
## ##
## def delvtuple2str(v, asap):
## 	"pretty-print [ vehicle, time(ASAP), ] tuples"
##
##	vs = is_special_vehicle(v)
##
##	return f'V[,ASAP={ asap }min]'  if not vs  else vs


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
## TODO: centralize deparsing/indexing
##
def mayreach2str(t):
	"pretty-print vehicle ID, primary, ASAP tuples"

	if len(t) == 2:
		return f'[VH={ t[0] },primary={ t[1] }]'

	return f'[VH={ t[0] },primary={ t[1] },ASAP={ t[3] }min]'


##--------------------------------------
def new_vehicle(vid):
	"Vehicle Status struct for newly assigned one"

	return {
		'primary':   0,
		'secondary': 0,
		'deliveries': {},
		'arrivals':   [],
		'refills':    [],
		'stops':      [],     ## schedule form of deliveries{}
	}


##--------------------------------------
## Backtrack Storage:
##    [ id, arrival of delivery(minutes), vehicle ID, cost(trip),
##      minutes_before ]
##
## backtrack stack contains one entry per level: this choice was taken.
##
## the corresponding 'backtrack alternates' stack contains all other
## possible choices at that level, which were _not_ taken (and they
## are to be enumerated once the original choice has been exhausted)


##--------------------------------------
## climb back in backtrack tree, returns next combination to evaluate
##
## sanity-check only, no output, unless asked for
##
## see 'Backtrack Storage' for description of backtrack entries
##
def show_backtrack(backtrack, btrack_alt, where=None):
	if len(backtrack) != len(btrack_alt):
		terminate('mismatched backtrack/alternatives depth (' +
		          f'depth(stack)={ len(backtrack) }, ' +
		          f'depth(alternates)={ len(btrack_alt) })')

	if (backtrack == []):
		debugmsg('## BACKTRACK STACK/S EMPTY', 1, type=vTRC_STACK)
		return False

	if debug_is_active(2, vTRC_STACK):
		print('====  BACKTRACK STACK')
		debugmsg(f"## BACKTRACK.STACK.DEPTH={ len(backtrack) }",
		         1, type=vTRC_SCHED | vTRC_STACK)
		for bi, btrck in enumerate(range(len(backtrack) -1, -1, -1)):
			print(f'## BACKTRACK.CHOICE[{ -1-bi }]=' +
				f'{ backtrack[ btrck ] }')
			print(f'## BTRACK.ALT.NR={ len(btrack_alt[-1-bi]) }')
			print(f'## BTRACK.ALT[{ -1-bi }]='
				f'{ btrack_alt[ btrck ] }')

	return True


##--------------------------------------
## returns initial/empty VRoute Status
##
def vehicle_cost0():
	"initial, all-empty state of per-vehicle route statistics"

	return {
		'primary':    0,
		'secondary':  0,
		'd_minutes':  [],
		'distances':  [],
		'stops':      [],
		'arrivals':   [],
		'deliveries': {},
		'checked':    {},
	}


##--------------------------------------
def dict_has_all_keys(d, k):
	if not d:
		return False

	k = list(dk  for dk in k  if (not dk in d))
	return k == []


##--------------------------------------
## expect at least a skeleton 'VRoute Status' struct
## returns text describing error, or False if everything is OK (expected)
##
## none of these test is ever expected to fail
##
def is_invalid_route(vroute):
	if not (dict_has_all_keys(vroute, ['primary', 'secondary', 'stops',
	                                   'd_minutes', 'distances',
	                                   'deliveries', 'arrivals', ])):
		return "Required VRoute field missing"

	if len(vroute['d_minutes']) != len(vroute['stops']):
		return "inconsistent segment minutes vs. route stops (count)"

	if len(vroute['distances']) != len(vroute['stops']):
		return "inconsistent route distances vs. route stops (count)"

				## stops' arrival minutes MUST be
				## chronological, and separated at least
				## by delivery overhead
				##
	arvmins = list(s[0]  for s in vroute['stops'])

	for i, amin in enumerate(arvmins[1:]):
		if (arvmins[i] + vTIME_DELIVER_MIN >= amin):
			return("insufficient delivery-to-delivery separation "+
				f" ({arvmins[i]} -> {amin} minutes)")
			##
			## >=; we assume there are no zero-dist deliveries,
			## so minimal route latency is vTIME_DELIVER_MIN +1

	return False


##--------------------------------------
## return updated 'best' if (1) previous-best was empty or (2) current
## route is an improvement
##
## local solutions only; storing best-current to global is
## register_best2global(), called once per vehicle
##
## output may be assigned to search-wide 'best' directly
##
## 'vroute' is VRoute Status of current solution; it MUST have already
## initialized all fields
##
def maybe_register_best(best, vroute, arrivals):
	if (not 'primary' in vroute):
		raise ValueError("unable to evaluate route")

	vprm1 = vroute[ 'primary' ]

	if (best == None) or (best['primary'] == 0):
		debugmsg(f"initial solution primary={ vprm1} " +
		         f"[unused: { MAX1 - vprm1 }]", 1, type=vTRC_PACK)
		return copy.deepcopy(vroute)

	##-----  sanity checks  ----------------------------------------------
## TODO: pretty-print both routes here

	if vprm1 > MAX1:
		raise ValueError("alleged route overloads primary " +
		                 f"limit: { vroute }")
	if best['primary'] > MAX1:
		raise ValueError("alleged previous-best route overloads " +
		                 f"primary limit: { best['primary'] }")

	riv = is_invalid_route(vroute)
	if riv:
		print(f"invalid deliveries: { vroute }")
		raise ValueError("alleged previous-best route is invalid " +
		                 f"({ riv })")

	##-----  /sanity checks  ---------------------------------------------

			## relative change: primary sum best-so-far/current;
			## total distance best-so-far/current (%)
			## note: higher is better
			##
	sum1_improve_pct = 100.0 * (vprm1 - best['primary']) / best['primary']

## TODO: cache distances, instead of repeated sum() invocations

	dist_best   = sum(best[ 'distances' ])
	dist_vroute = sum(vroute[ 'distances' ])
	dist_improve_pct = 100.0 * (dist_vroute - dist_best) / dist_best
			##
			## a populated 'best' already stores at least one
			## delivery, therefore a path > 0.0: no div-by-zero

	debugmsg(f"## ? SUM(PRIMARY): {best['primary']} -> " +
		 f"{ vprm1 } ({ sum1_improve_pct :0.1f}%)?",
	         3, type=vTRC_PACK)
			##
	debugmsg(f"## ? DIST.TOTAL: from {dist_best :.6f} -> " +
		 f"{ dist_vroute :.6f} ({ dist_improve_pct :.1f}%)?",
        	 3, type=vTRC_PACK)

	improves = False
			## add heuristics here as if...else... chain
			## set to True if current plan is considered better


	if (sum1_improve_pct >= 0.5) and (dist_improve_pct > -1.0):
		debugmsg(f"solution improves primary { best['primary'] }->" +
		         f"{ vprm1 } [unused: { MAX1 - best['primary'] }->" +
		         f"{ MAX1 - vprm1 }]", 1, type=vTRC_PACK)
		improves = True


	elif (sum1_improve_pct >= -0.5) and (dist_improve_pct >= 2.5):
		explain = ''
		if sum1_improve_pct < 0.0:
			explain =  ' with modest efficiency loss '
			explain += f' ({ -sum1_improve_pct :.1f}%)'

		if (dist_improve_pct > 0.0):
			dchg = 'changes'
		else:
			dchg = 'reduces'

		debugmsg(f"solution {dchg} total distance { dist_best :.6f}->"+
		         f"{ dist_vroute :.6f}" +explain,
		         1, type=vTRC_PACK)
		improves = True

					## .deepcopy() needed:
					## loop around this vehicle updates
					## routing cost in 'vroute' struct
					## in subsequent iterations (if just
					## copied to 'best', which passes
					## by reference)
					##
					## save+freeze current state

	return copy.deepcopy(vroute)  if improves  else best


##--------------------------------------
def delv_arrival_status(vid, arrival_minute):
	return {
		'vehicle': vid,
		'minute':  arrival_minute,
	}


##--------------------------------------
## sets Delivery Arrival Status for delivery 'id', vehicle ID 'vid'
##
def register_arrival(arrivals, id, vid, arrival_minute):
	assert(arrivals != None)

	if not tVID2TIME in arrivals:
		arrivals[ tVID2TIME ] = {}

	if not vid in arrivals[ tVID2TIME ]:
		arrivals[ tVID2TIME ][ vid ] = {}

## TODO: check for final assignments
## intermediate search MAY legitimately assign inconsistent values
## while searching
##	if id in arrivals[ tVID2TIME ][ vid ]:
##		if arrivals[ tVID2TIME ][ vid ][ id ] != arrival_minute:
##			raise ValueError(f"inconsistent vehicle/id/arrival "
##					"combination vid={vid},delv={id}")
##	else:
	arrivals[ tVID2TIME ][ vid ][ id ] = arrival_minute

	arrivals[ id ] = delv_arrival_status(vid, arrival_minute)


##--------------------------------------
## summarize current plan for vehicle 'vid'
##
## see also: register_best2global(), which is the complete form
## this fn may get called with incomplete plans too
##
def report_plan(vroute, vid, marker=''):
	for dlvi, delv in enumerate(vroute[ 'stops' ]):
		minute, id = delv[0], delv[1]

		print(f"## SCHED{marker} VEH={ vid },T={ minute }min," +
			f"DELV={ id },STOP={ dlvi+1 }")


##--------------------------------------
## mark route in 'best' as taken, sanity-checking its constituents
##   1) none of the deliveries in 'best' may have already been
##      assigned to other vehicles
##   2) delivery times are non-decreasing, compatible with layout
##      plus overhead times
##
## TODO: remaining sanity checks
## see also: report_plan()
##
def register_best2global(arrivals, best, vid):
	assert(arrivals != None)
	assert('stops' in best)

## TODO: check-consistent-best (f.ex. primary <= MAX1)

	unused1 = MAX1 - best[ 'primary' ]

## TODO: is this after adding everything?
	print(f"## BEST.LOAD.PRIMARY.VEH[{ vid }]={ best[ 'primary' ] }")
	print(f"## BEST.LOAD.UNUSED.VEH[{ vid }]={ unused1 }")
	print(f"## BEST.LOAD.UNUSED.VEH[{ vid }].PCT=" +
		f"{ (100.0 * unused1 / MAX1) :.1f}")

	print(f"## LOAD.SECONDARY.VEH[{ vid }] = { best[ 'secondary' ] }")

	for dlvi, delv in enumerate(best[ 'stops' ]):
		minute, id = delv[0], delv[1]

		print(f"## SCHED VEH={ vid },T={ minute }min,DELV={ id }," +
			f"STOP={ dlvi+1 }")

## TODO: eval route; times must be increasing

		if (id in arrivals) and (vid != arrivals[id][ 'vehicle' ]):
			print(f'## ARRIVAL: vehicle ID differs: { vid }->' +
				f"{ arrivals[id][1] }")

			raise ValueError("assign-to-best ID already set")

		register_arrival(arrivals, id, vid, minute)


##--------------------------------------
## register vehicle at (X,Y), in ASAP minute it can leave,
## based on the last entry of backtrace stack
##
def vehicle_at():
	pass


##--------------------------------------
## returns ASAP(leave), X, Y of last vehicle stop if present
##
## now_min, None, None if no vehicle stops
## calling code MUST manage cases of no past history
##
## 'vroute' is VRoute Status struct
## 'now_min' is current time, in minutes
##
def vehicle_last_at(vroute, now_min):
	if vroute and vroute[ 'stops' ]:
## TODO: symbolic veh.history-to-value(index) symbolic constants
		leave_asap_min =  vroute[ 'stops' ][-1][0]
		leave_asap_min += vTIME_DELIVER_MIN
					##
## TODO: symbolic veh.history-to-value(index) symbolic constants
		x, y = vroute[ 'stops' ][-1][ -2: ]
		x, y = float(x), float(y)

		return leave_asap_min, x, y

	return now_min, None, None


##--------------------------------------
## return >0  if existing assignments prevent delivery
##        0   if delivery does not conflict with any constraint
##
## specific error codes:
##     (1) may not be delivered in immediate future (vNEXTUNITS; tmask)
##     (2) delivery is already assigned (other vehicles)
##     (3) delivery is already present in current route (this vehicle)
##     (4) delivery is not suitable for this vehicle
##
## 'd'     is delivery being checked
## 'dels'  is auxiliary delivery struct
## 'tmask' is time window of possible delivery to consider
## 'vbit'  is bitmask of current vehicle; cross-checked against vehicle
##         bitmask of deliveries
##
def unsuitable_delivery(d, dels, vroute, arrivals, tmask, vbit):
	if (d == None) or not dels:
		return 666              ## required params missing completely

	if ((tmask & d[ 'time2vec' ]) == 0):
		return 1                ## no common time

## TODO: centralized timevectors-intersection which can
## deal with multiple ASAP times
##
## example:
##       ----1111-----1111-----   time vector
##       ------1111111111111111   "may arrive"  ->
##       ------1------1--------   both are 'ASAP', one for each vector
## (obv never an issue if time vectors are without holes)
##
## counterexample:
##       ----1111-----1111-----   time vector
##       ----------11----------   "may arrive" ->
##                                no suitable arrival, even if
##                                min(t.vector) <= arrival <= max(t.vector)

	if (d["index"] in arrivals):
		return 2                ## delivery is already assigned
		                        ## (not to current vehicle)

	if (d["index"] in vroute["deliveries"]):
		return 3                ## already assigned, to current
		                        ## vehicle

	if (not 'vehicle_may' in d) or ((vbit & d[ 'vehicle_may' ]) == 0):
		return 4                ## this vehicle can not deliver

	return 0
## TODO: original, inline version
					## find which deliveries:
					## (2) are not yet assigned,
					##     either by other vehicles (2.1)
					##     or already in the current
					##     vehicle route (2.2)
					## (3) may be assigned to  this vehicle
					## (4) do not overload vehicle
					##
					## also, checked subsequently,
					## (5) vehicle may actually
					##     get there within (1)
					##


##--------------------------------------
## Vehicle-Delivery data
## when considering routes, the following records are stored:
##
## [ delivery index; primary sum incl. that of delivery; vehicle ID;
##   minutes(ASAP/arrival), minutes(position before being routed) ]
##
## vehicle ID is redundant, as it is fixed during routing each vehicle
## it is simply included as diagnostics aide
##
## [198, 901741130, 'VEHICLE00', 30, 0]  ->
##    index(198); load(VEHICLE00) == 901741130;
##    arrives at (+)30 minutes; was at (0) when dispatched


##--------------------------------------
## full list of deliveries within near future from 'now_min' time point
## location determined by last delivery in vroute['stops'] if present
##
## now_min 0 is default:
##   - any time if no deliveries scheduled yet
##   - earliest leave time from vehicle route if vroute is not empty
##
## 'dels' is global delivery-list struct; read-only
## 'vbit' is bitmask-ID of current vehicle
##
def delivery_candidates(vroute, dels, arrivals, vbit, vehicle_id, now_min=0,
                        lookahead_units=vNEXTUNITS):
	if now_min == 0:
		if vroute[ 'stops' ]:
			now_min = vroute[ 'stops' ][-1][0] +vTIME_DELIVER_MIN
## TODO: remove magic indexes
		else:
			pass

	swe_min = now_min +vTIME_UNIT_MINS * lookahead_units -1
					## search-window-end; minutes

	tmask =  (minute2timevec(swe_min) << 1) -1
	tmask -= minute2timevec(now_min) - 1
					## immediate-future time units
					## where we consider deliveries

	debugmsg(f'## T.NOW={ minute2wall(now_min) }(m={ now_min })',
	         1, type=vTRC_SCHED)
	debugmsg(f'## T.MAX.NOW={ minute2wall(swe_min) }(m={ swe_min })',
	         1, type=vTRC_SCHED)
	debugmsg(f'## T.MASK=x{ tmask :x}', 2, type=vTRC_SCHED)

					## find which deliveries:
					## (1) may be delivered in immediate
					##     future (vNEXTUNITS; tmask)
					## (2) are not yet assigned,
					##     either by other vehicles (2.1)
					##     or already in the current
					##     vehicle route (2.2)
					## (3) may be assigned to  this vehicle
					## (4) do not overload vehicle
					##
					## also, checked subsequently,
					## (5) vehicle may actually
					##     get there within (1)
					##
	ds = list(d  for d in dels
	          if not unsuitable_delivery(d, dels, vroute, arrivals,
	                                     tmask, vbit))

					## 'may reach'
					## (index, primary) tuples in
					## decreasing primary order
					## which do not overload vehicle
					##
	mr = sorted(([ d["index"], d["primary" ], ]
	 	       for d in ds
		       if (d["primary"] + vroute["primary"] <= MAX1)))   ## (4)
##
## TODO: anything changing here with multiple ASAP minutes?
## see unsuitable_delivery() for example

	mr = sorted(mr, key=operator.itemgetter(1), reverse=True)
					## decreasing primary order


	debugmsg(f'## SCHED.NOW.CANDIDATES0.COUNT={ len(mr) }',
	         1, type=vTRC_SCHED)
	debugmsg('## SCHED.NOW.CANDIDATES0=' +
	         ','.join(mayreach2str(m) for m in mr),
	         2, type=vTRC_SCHED)

					## turn [ idx, primary ] to
					## [ index, primary, ASAP(min) ]
					## tuples
	if vroute['stops']:
		leave_asap, x, y = vehicle_last_at(vroute, now_min)

		mrn = []
		for di, add in mr:
			twindow = tmask & dels[di]['time2vec']
			dx, dy = dels[di]['x'], dels[di]['y']

			asap = xy2asap_minute(x, y, dx, dy, leave_asap, twindow)
## TODO: multi-valued; returns list of ASAP minutes

			nroute = ''
					## did we already consider the current
					## route + (newly tested delivery)
					## as an option? if so, skip it
			if asap != None:
				nroute = vroute2normalized(vroute, di, asap)
				if nroute in vroute[ 'checked' ]:
					debugmsg(f'## SCHED.WAS.SEEN={nroute}',
	         			         2, type=vTRC_SCHED)
					asap = None

						## (5) vehicle may actually
						##     get there to hit (1)
						## see conditions above
			if asap != None:
				debugmsg(f'## SCHED.FULL.NEW={nroute}',
				         2, type=vTRC_SCHED)
				mrn.append([ di, add, vehicle_id, asap,
				             now_min, ])
	else:
						## starting new vehicle: can
						## reach start of window
		mrn = []
		for di, add in mr:
			twindow = tmask & dels[di]['time2vec']

			mrn.append([ di, add, vehicle_id,
			    timevec2asap(twindow, minutes=True), now_min,
			])

## TODO: check for return-to-base as an option

	debugmsg(f'## SCHED.NOW.CANDIDATES.COUNT={ len(mrn) }',
	         1, type=vTRC_SCHED)
	debugmsg('## SCHED.NOW.CANDIDATES=' +
	         ','.join(mayreach2str(m) for m in mrn),
	         2, type=vTRC_SCHED)

	return mrn


##--------------------------------------
## are there any semi-reasonable deliveries, or is this vehicle
## out of options?
##
## called when no immediate candidates are detected in near-future window
##
## 'maxu' is XXX
##
def no_feasible_future_delv(delvs, vroute, arrivals, now_min, maxu):
	debugmsg('## MAIN.LOOP, CHECK FOR FEASIBUTE FUTURE',
        	 3, type=vTRC_FLOW)

	future = timevec2after(minute2timevec(now_min), maxu)

					## collect [id, primary,] for
					##   (A) yet-unassigned deliveries
					##   (B) in any future unit
	pending_min1 = list(
			d['primary']  for d in delvs
			if ((not d['index'] in arrivals) and             ## (A)
			    (future & d['time2vec']))                    ## (B)
	)

					## if primary fill + min(remaining
					## delivery) is > primary.threshold,
					## this vehicle is full
					##           -> return to base
					##
					## note: we do not check for
					## reachability; just expect any of
					## the other checks to trigger
					## 'at some point' if unreachable

	if pending_min1:
		pending_min1 = min(pending_min1)
		debugmsg(f'## PACK.MIN(REMAIN)={ pending_min1 }',
		         2, type=vTRC_SCHED)

	else:
		pending_min1 = MAX1 *2
				## arbitrary value which
				## triggers 'to much to fit'
				## below

				## is this a final combination?

	if (pending_min1 + vroute[ "primary" ] > MAX1):
		debugmsg('## PACK.COMPLETE=no-next-fit',
		         1, type=vTRC_SCHED)
## TODO: evaluate return-to-base

		return True

	return False


##--------------------------------------
def assert_backtrack_stacks(backtrack, alt):
	if len(backtrack) != len(alt):
		terminate("inconsistent backtrack-stack size: "+
			f"main { len(backtrack) }, aux. { len(alt) }")


##--------------------------------------
## raise exception, returning False, if anything inconsistent
## silently tolerates None 'vcost'
##
def assert_vroute_is_sane(vcost):
	if vcost == None:
		return True

## TODO: now we have dict_has_all_keys(d, k)
##
	if ((not 'stops' in vcost) or (not 'distances' in vcost) or
	    (not 'd_minutes' in vcost) or (not 'deliveries' in vcost) or
	    (not 'arrivals' in vcost)):
		raise ValueError(f'missing route-related fields (r={vcost})')

	if len(vcost[ 'd_minutes' ]) != len(vcost[ 'distances' ]):
		raise ValueError('inconsistent duration/distance data' +
		                 f'(r={vcost}')

	if len(vcost[ 'stops' ]) != len(vcost[ 'distances' ]):
		raise ValueError('inconsistent duration/stop-list ' +
		                 f'(r={vcost}')

	if len(vcost[ 'stops' ]) != len(vcost[ 'deliveries' ]):
		raise ValueError('inconsistent duration/stop-list ' +
		                 f'(r={vcost}')

	if len(vcost[ 'd_minutes' ]) != len(vcost[ 'arrivals' ]):
		raise ValueError('inconsistent arrivals/inverted.index' +
		                 f'(r={vcost}')

## TODO: conditional: check sum() for primary and secondary

	return True


##--------------------------------------
## roll back VRoute Status, when backtracking one level
## update 'vcost' in place
## removes entry from 'arrivals' if non-None
##
def vroute_backtrack1(vcost, dels, arrivals=None):
	if vcost == None:
		return

	assert_vroute_is_sane(vcost)

	curr = vcost[ 'stops' ].pop(-1)         ## delivery we are undoing
	                                        ## that in 'curr' etc.

	arrv_minute, id, x, y = curr

	if arrivals:
		if not id in arrivals:
			raise ValueError(f"undoing yet-unseen delivery {id}")
		del(arrivals[ id ])

	assert(len(dels) > id)
## TODO: centralized consistency checking

	rm1, rm2 = dels[id][ 'primary' ], dels[id][ 'secondary' ]
		##
	if vcost[ 'primary' ] < rm1:
		raise ValueError('inconsistent delivery queue (primary)')
	vcost[ 'primary' ] -= rm1

	if vcost[ 'secondary' ] < rm2:
		raise ValueError('inconsistent delivery queue (secondary)')
	vcost[ 'secondary' ] -= rm2

## TODO: ensure ID is present and matches expected
	del(vcost[ 'deliveries' ][ id ])

## TODO: final check: route is empty with all-0 sums etc.

	vcost[ 'distances' ].pop(-1)
	vcost[ 'd_minutes' ].pop(-1)
	vcost[ 'arrivals'  ].pop(-1)


##--------------------------------------
## did 'enough time' pass since last checkpoint (such as filling a new vehicle?)
## 'tbase' must have been filled with time.perf_counter()
##
def are_in_timeout(tprev):
	tdelta_ms = timediff_msec(tprev, time.perf_counter())

	return (tdelta_ms >= vTIMEOUT_MSEC)


##=====  SAT solver things  ==================================================
## see codingnest.com/modern-sat-solvers-fast-neat-underused-part-1-of-n/
## for a general introduction to expression encoding for SAT solvers.
##
## subordinate CNF-related code is in dev/satcnf.py
##
## SAT Booleans are partially redundant, to allow use of simpler formulas:
##   d0t2          delivery #0, time unit #2 features delivery
##   d0t2v0..vN    delivery #0, time unit #2, nr. of delivering vehicle,
##                 binary-encoded (big-endian; vN is least significant).
##                 features +1 vehicles: all-0 corresponds to 'no delivery'
##   v0t2          vehicle #0 delivers in time unit #2
##
## cross-references added:
##   d0t2        <=>  d0t2v0..vN    is real delivery
##   d0t2v0..vN  <=>  v...t2        for vehicle id=(v0..vN)
##   d0t2v0..vN  <=>  NOT d...t...  for other deliveries+units which would
##                                  conflict -> temporal separation


##-----------------------------------------
sNALL0 = 'NZ'                     ## suffix for not-all-(values-)zero +variable
sNALL1 = 'ALL1'                   ## suffix for all-(values-)one +variable


##-----------------------------------------
## XOR of two bits; 'negate' chooses XNOR
##
## sample: A; B; N = A ^ B
##     1) A | B | not(N)             N -> (A | B)
##     2) not(A) | N       together: (A | B) -> N
##     3) not(B) | N
##
## None 'result' auto-assigns variable name if necessary
## returns list of clauses, name of final variable, + comment
##
def satsolv_xor1(var1, var2, result=None, negate=False):
	cls = []

	if result == None:
		negstr = 'n'  if negate  else ''
		result = f'{ var1 }_{ negstr }x_{ var2 }'

	if negate:                     ## X(N)OR only swap truth table polarity
		pol = [ ' ', '-', '-', ' ', ]
	else:
		pol = [ '-', ' ', ' ', '-', ]

	cls.extend([                         ## truth table for "{lf} XOR {rg}"
		f' {var1}  {var2} { pol[0] }{ result }',
		f'-{var1}  {var2} { pol[1] }{ result }',
		f' {var1} -{var2} { pol[2] }{ result }',
		f'-{var1} -{var2} { pol[3] }{ result }',
	])

	negstr = 'NOT '  if negate  else ''

	return cls, result, f'{ result } := { negstr }({var1} XOR {var2})'


##-----------------------------------------
## NAND, for two bits
##
## sample: A; B; N = not(A & B)
##     1) not(A) | not(B) | not(N)
##     2)      A | N
##     3)      B | N
##
## None 'result' auto-assigns variable name
## returns list of clauses + comment
##
## TODO: merge with AND
##
def satsolv_nand1(var1, var2, result=None):
	cls  = []

	if result == None:
		result = f'{ var1 }_nn_{ var2 }'

			## placeholders, for column alignment
			## incl. +1 column since aligns with negated column
	v1p = ' ' * (len(var1) +1)
	v2p = ' ' * (len(var2) +1)

	cls.extend([
		f'-{var1} -{var2} -{result}',
		f' {var1} { v2p }  {result}',
		f' {var2} { v1p }  {result}',
	])

	return cls, result, f'{ result } := ({var1} NAND {var2})'


##-----------------------------------------
## raw clauses for two-input OR
##
## returns assigned variable and clauses
## TODO: sync assign-in results, then adapt to that
##
def satsolv_or1(var1, var2, result, negate=False):
		## sign for -R/R

## TODO: obsoleted if split properly -> separate ''/- fields

	rsign1, rsign2 = ('', '-')  if negate  else ('-', '')
		## sign(R) in all-enclosing (1) and per-variable (2) lines

	return result, [
#		[ ' ', var1, ' ', var2, '-', result ],
#		[ '-', var1, ' ', result,           ],
#		[ '-', var1, ' ', result,           ],

		f' {var1} {var2} { rsign1 }{result}',
		f'{ rsign2 }{var1} {result}',
		f'{ rsign2 }{var2} {result}',
	]


##-----------------------------------------
## sample: A; B; ...; R = A | B | ...
##     1) A | B | not(R)      not(A) & not(B) -> not(R)
##     2) not(A) | R          A -> R; B -> R  ...
##     3) not(B) | R
##        ...
##
## NOR with 'negate' (negates R in all clauses)
##
## returns list of clauses + control variable + comment
##
def satsolv_or(base, vars, result=None, negate=False):
	cls = []
	v   = list(vars)     ## TODO: sorted(vars) canonical order?

	if result == None:
		result = base + sNALL0

	rsign1, rsign2 = ('', '-')  if negate  else ('-', '')
		## sign(R) in all-enclosing (1) and per-variable (2...) lines

## see also: satsolv_or1()
	all = list((base +b)  for b in  v)
	all.append(f"{ rsign1 }{ result }")
		##
	cls.append( " ".join(all) )                   ## A | B | not(N)

	terms = list((base +b)  for b in v)

	cls.extend((f'-{ t } { rsign2 }{ result }')  for t in terms)

	if negate:
		req = f'NOR(' +(",".join(terms)) +')'
	else:
		req = f'(' +(" OR ".join(terms)) +')'

	return cls, result, f'{ result } := { req }'


##-----------------------------------------
## sample: A; B; N = A & B
##     1) not(A) | not(B) | N            N -> (A & B)
##     2) A | not(N)           together: (A & B) -> N
##     3) B | not(N)
##
## None 'result' auto-assigns variable name
## returns list of clauses + comment
##
def satsolv_and(base, vars, result=None):
	cls = []
	v   = sorted(vars)

	if len(vars) == 1:
		return vars[0], vars[0], f'AND({ vars[0] }) == { vars[0] }'

	if result == None:
		result = base + sNALL1

	all = list((f"-{ (base +b) }")  for b in  v)
	all.append(result)
		##
	cls.append( " ".join(all) )                   ## not(A) | not(B) | N

	terms = list((base +b)  for b in v)

	cls.extend((f'{ t } -{ result }')  for t in terms)

	return cls, result, f'{ result } := (' +(" AND ".join(terms)) +')'


##-----------------------------------------
## return 2x list, of signs ('-' or empty) and of sign-less IDs
## input is list of text IDs
##
def satsolv_str2ids(ids):
	sgns = list(('-'  if (i[0] == '-')  else '')  for i in ids)
	curr = list(re.sub('^-', '', i)  for i in ids)

	return sgns, curr


##-----------------------------------------
## SAT/CNF: are two variable collections identical?
## used to cross-check possibly conflicting deliveries, with two N-bit
## configurations: different delivery + time(unit) + vehicle index(N-bit):
##   (1) either one of the indexes is all-0: not yet assigned
##   (2) N-bit value 1 != N-bit value 2 (-> assigned to different vehicles)
##
## inputs are collections of variables of identical size
##
def satsolv_differ_n(var1, var2, result=None):
	if (not var1) or (not var2) or (len(var1) != len(var2)):
		raise ValueError("inconstent bitvectors-differ input")

	comment = ''
	return [], result, comment


##-----------------------------------------
def satsolv_nr_of_added_vars(sat):
	return sat[ 'added_vars' ]  if (sat and ('added_vars' in sat))  else 0


##-----------------------------------------
## increase the number of solver-allocated, intermediate variables
##
def satsolv_register_added_vars(sat, n=1):
	sat[ 'added_vars' ] += n


##-----------------------------------------
## centralized NOT, to save on recurring logs
##
## just a macro to document NOT-X invocations
## does not need extra variables, just an inverting clause
##
def satsolv_not(sat, var):
	rv = f'-{var}'

	return rv, rv, f'NOT({ var })'


##-----------------------------------------
## NAND, for arbitrary nr of bits
##
## sample: A; B; C; D; N = not(A & B & C & D)
##     1) not(A) | not(B) | not(N)
##     2)      A | N
##     3)      B | N
##     4)      ...
##
## None 'result' auto-assigns variable name
## returns list of clauses, result variable, comment
##
def satsolv_nand_n(sat, vars, result=None):
	cls  = []

	if len(vars) == 1:
		return satsolv_not(sat, vars[0])

	if result == None:
		result = satsolv_new_varname(satsolv_nr_of_added_vars(sat) +1)

	vall = list(f'-{v}'  for v in vars)

	cls.append([ ' '.join(vall) + f' -{result}' ])
	cls.extend([ f' {v} {result}' ]  for v in vars  )        ## 1x each bit

	return cls, result, f'{ result } := NAND({ ",".join(vars) })'


##----------------------------------------------------------------------------
## collapse list to runs of identical entries
##     [ 1, 0, 1, 1 ]  ->  [ [1], [0], [1, 1] ]
##
def arr2runs(arr):
	runs = []

	for v in arr:
		if (runs == []) or (runs[-1][-1] != v):
			runs.append([])
		runs[-1].append(v)

	return runs


##----------------------------------------------------------------------------
## expressions compare up to two runs' worth of bits, comparing only
## bits of the most significant runs against the big-endian bit array 'vars'
##
## first run always from an all-1 region
##
## assume V is the variable's value, the three cases below compare:
##     V  <  1  0000..000
##     V  <  1111..111                         all-ones
##     V  <  111..11   000..00
##
## 'runs' in the above cases: [ [1],        [0,0,...0,0]   ]
##                            [ [1,1,1,...,1]              ]
##                            [ [1,1,..,1], [0,0,0,...0,0] ]
## 'nbits' is the printable-collapsed form, 100..00, 111..111 etc.
##
## returns None, None, None  if no more runs
## registers any intermediate variables
##
def satsolv_less_than_2x(sat, vars, runs, nbits):
	if runs == []:
		return None, None, None

	if runs[0][0] != 1:
		raise ValueError("bits<N did not start with all-1 bit run")

## TODO: this special-casing of single bits disappears, once _nand_n()
## centralizes all <3 special-cased cases: can pass 1-bit comparison
## through as-is

	vdescr = 'VARS:' +(".".join(vars))

	if (len(runs) == 2) and (len(runs[0]) == 1):   ## 100..00 -> direct bit
		result = vars[0]                ## no additional condition/var
		cls    = [ f'-{result}' ]
		xcomm  = f'{result}: ({vdescr} < { nbits }b)'

	elif (len(runs) <= 2):
				## 11100..000 -> NAND(...3 MS variables...)
				## 11111..111 -> NAND(...all variables...)
				##
				##
				##
		bits2cmp = vars[ : len(runs[0]) ]
		cls, result, xcomm = satsolv_nand_n(sat, bits2cmp)
				##
		satsolv_add_vars(sat, [ result ])
				##
		xcomm += f': ({vdescr} < { nbits }b)'

	elif (len(runs) == 3) and (len(runs[-1]) == 1):
				## straightforward case:
				##   n <= 11..100001  exactly three runs; LS one
				##                    is a single bit
				##
				## construct comparison from:
				##   (1) AND(...MS bit/s...)
				##         -> if not, value < pattern
				##   (2) OR(...all-0 runs' bits below...)
				##         -> if yes, value > pattern
				##   (3) ...comparison of LS bit...
				##         -> if yes, value > pattern
				##
				## comparison is hierarchical:
				##   (1) not-AND(1)         -> value < pattern
				##   (2) AND(1)  AND  OR(2) -> value > pattern
				##   (3) AND(1)  AND  NOT(OR(2))  AND
				##          not-AND(3)      -> value < pattern
				##
				## with minor additions, would also extrapolate
				## to three runs, with >1 bits in LS one: just
				## adds a less-than-X term for the LS run
				##
		msvars  = vars[ : len(runs[0]) ]   
		midvars = vars[ len(runs[0]) : ]
		lsvars  = vars[ len(runs[0])+len(runs[1]) : ]

		mscls, mscmp, mscomm = satsolv_and('', msvars)
##		satsolv_add_vars(sat, [ mscmp ])
				##   (1) -> mscmp

		midcls, midcmp, midcomm = satsolv_or('', midvars)
##		satsolv_add_vars(sat, [ mscmp ])
				##   (2) -> midcmp

		lscls, lscmp, lscomm = satsolv_and('', lsvars)
##		satsolv_add_vars(sat, [ mscmp ])
				##   (3) -> lscmp

		cls, result, xcomm = None, None, None

	else:
		raise ValueError("need a generic SAT/range comparison here")

	return cls, result, xcomm


##----------------------------------------------------------------------------
## is the binary combination of 'vars' < N?
## register expression to SAT variables+clauses
##
## 'vars' is bit variables, most to least significant
##
## registers any newly allocated variables to 'sat'
##
## TODO: proper binary comparison, then Quine McCluskey etc. reduction
## TODO: right now, we just pick predefined patterns
##
## since pack-n-route currently leaves only unallocated deliveries to
## the SAT solver, we expect to see not more than 3 (maybe 4)-bit variables
##
def satsolv_less_than(sat, vars, n):
	nbits = f'{ n :b}'
	nb    = list(int(b)  for b in nbits)

	if len(nbits) >= (1 << len(vars)):     ## N is wider than 2^...bits...
		return                         ## always succeeds

	runs = arr2runs(nb)

	assert(runs != [])
	assert(runs[0][0] == 1)                ## nb[] has no MS zeroes

	result, cls, xcomm = satsolv_less_than_2x(sat, vars, runs, nbits)

	## ...any special logging etc. would happen here...

	return cls, result, xcomm


##----------------------------------------------------------------------------
## are the values equal, or either one is all-0?
##
## comparison for check "are A and B equal, or is at least one of them
## unassigned?" if all-0 is reserved for unassigned
##
## turns into
##    NOR(v1) | NOR(v2) | NOT-EQ(v1, v2)
##    ->
##    NOR(v1) | NOR(v2) | OR(XOR(v1, v2))
##
## single-bit version simplifies to
##    NAND(v1, v2)     -- only the 1/1 pair is invalid
##
## returns list of clauses, result variable, comment
##
def satsolv_neq_or0(sat, v1, v2, result=None):
				## TODO: OR extra bits which are
				## in v1 or v2 only -> extra term in top clause
	if len(v1) != len(v2):
		raise ValueError("NEQ-OR0(...different sized vectors...")

	if len(v1) == 1:
		nv  = satsolv_new_varname2(sat, prefix='NAND')
		cmt = 'NEQ-OR0({ v1[0] } / { v2[0] }) -> NAND'
		return satsolv_nand1(x, y, result=nv)

	nor1 = satsolv_new_varname2(sat, prefix='NOR')
	nor2 = satsolv_new_varname2(sat, prefix='NOR')
		##
	cls,  _, _ = satsolv_or('', v1, negate=True, result=nor1)
	cls2, _, _ = satsolv_or('', v2, negate=True, result=nor2)
		##
	cls.extend(cls2)

	xvars = []
				## XOR(...bits of v1..., ...bits of v2...)
				##
	for x, y in zip(v1, v2):
		xv = satsolv_new_varname2(sat, prefix='XOR')

		cls3, _, _ = satsolv_xor1(x, y, result=xv)
		cls.extend(cls3)
		xvars.append(xv)

				## OR(...above XOR bits...)
				## -> 1 if any XOR is 1 -> at least 1 bit diff
				##
	neq = satsolv_new_varname2(sat, prefix='NEQ')
	cls4, _, _ = satsolv_or('', xvars, result=neq)

	cls.extend(cls4)

	if result == None:
		result = satsolv_new_varname2(sat, prefix='NEQ_OR0')

				## NOR(1) NOR(2) OR(XOR(...)) -> NEQ-OR0
				##
	cls5, _, _ = satsolv_or('', [ nor1, nor2, neq ], result=result)

	cls.extend(cls5)

	cmt = f'NEQ-OR0({ ",".join(v1) } / { ",".join(v2) })'

	return cls, result, cmt


##-----------------------------------------
## return mapping table for string-to-int conversion for CNF specification
##
## inputs is all-numeric strings, standalone, or whitespace-separated clauses
## 'DDD' for True, '-DDD' for False values
##
## non-None 'values' is checked for already-assigned value; not updated
## caller must use .update(...result...) to merge new assignments
##
def satsolv_strings2ints(vars, values=None, first=1):
	res = {}
	for r in vars:
				## split to sign ('-' or empty) and base string
		_, curr = satsolv_str2ids(r.split())

		for id in curr:
			if values and (id in values):
				continue

			if not (id in res):
				res[ id ] = first
				first += 1
	return res


##-----------------------------------------
## registers name with non-None 'sat'
##
def satsolv_new_varname(nr=0, sat=None):
	vname = f'{ sSAT_2ND_VAR }{ nr +1 }'

	if sat:
		satsolv_add_vars(sat, [ vname ])

	return vname


##-----------------------------------------
## auto-registers next name with given prefix and solver-derived var.number
##
def satsolv_new_varname2(sat, prefix=sSAT_2ND_VAR):
	nname = satsolv_nr_of_added_vars(sat) +1
	nname = prefix +str(nname)

	satsolv_register_added_vars(sat, 1)
	satsolv_add_1var(sat, nname)

	return nname


##-----------------------------------------
## partition l into (roughly) k-sized parts
##
## in Python v3.12+, this will be itertools.batched()
##
def list2split(l, k):
	return [l[ i*k : (i+1)*k ]
		for i in range((len(l) +k -1) // k)]


##-----------------------------------------
## comment for 1-of-N to ...result... SAT clause/s
## 'vars' is list of input variables
##
## TODO: where do we special-case N=1, things like that?
##
def sat_1ofn_comment(res, vars):
	vlist = ",".join(vars)

	return f'1-of-N[={ len(vars) }]: ({ res }) for ({ vlist })'


##-----------------------------------------
## Return '(top-level) commander variable', newly added (commander) variables,
## related additional clauses, and comments documenting the collection.
##
## The first element of the commander-variable array is true if and only
## exactly one of 'vars' (variable-name) inputs is True.
##
## commander variables are named 'CMDR...'; prefix MUST NOT be used by others
## TODO: current form restricted to a binary tree
##       may specialize if truth table generator for k>2 fanout is available
##
## 'nr' is the number of defined additional variables, incl. current inputs
## (used in assigning IDs to intermediate ones)
##
## see
## Kliebert, Kwon: Efficient CNF encoding for selecting 1 of N objects,
## www.cs.cmu.edu/~wklieber/papers/
##     2007_efficient-cnf-encoding-for-selecting-1.pdf
## [accessed 2023-02-24]
##
def satsolv_1n(sat, vars, nr=0, allow0=False, result=None):
	if vars == []:
		raise ValueError("called with empty variable list")

	##-----  trivial special cases  --------------------------------------
	if len(vars) == 1:
		return vars[0], [], [], ''

	if len(vars) == 2:              ## -> A XOR B  or  A NAND B (if allow-0)
		cmd = result  if result  else f'{ sSAT_2ND_VAR }{ nr +1 }'

		if allow0:
			cls, _, _ = satsolv_nand1(vars[0], vars[1], result=cmd)
			cmt = f'at-most-1({cmd}) => ({vars[0]} NAND {vars[1]})'

		else:
			cls, _, _ = satsolv_xor1(vars[0], vars[1], result=cmd)
			cmt = f'at-most-1({cmd}) => ({vars[0]} XOR {vars[1]})'

		return cmd, [ cmd, ], cls, cmt

	##--------------------------------------------------------------------
## TODO: should be factored out, since other expressions may reuse
##       hierarchical grouping+var.assignment

			## recurse: build bottom-up grouping
			## 1st level: groups of original inputs
			## 2nd level: commander variables of 1st level groups...

			## TODO: fixed to fanout of 2
	grps  = list2split(vars, 2)
	grps0 = grps[:]    ## originals; allow modification of grps[]

	assign, newvar = [], []
			## assign[] collects [ ...group..., [ cmd.var ] ] list,
			## in assignment (bottom up) order
	cls = []

			## if a variable is alone in its group,
			## propagate it directly up.  in this case, the
			## originating group remains empty, and we only
			## store  [ [], [ ...variable... ] ] to assign
	while grps:
		curr = []
		for g in grps:
			if len(g) == 1:
				assign.append([ [], g[0] ])
				curr.append( g[0] )
				continue

			nv = satsolv_new_varname(nr +len(newvar) +1 )
			newvar.append(nv)
				##
			assign.append([ g, nv, ])
			curr.append(nv)
				##
			satsolv_add_comment(sat,
				f'  1-of-N {nv} = OR+not-NAND({",".join(g)})')

		if len(curr) == 1:
			break
		grps = list2split(curr, 2)   ## advance to next level

	if result:
		assign[-1][-1] = result      ## caller-supplied top var.name
		newvar.pop(-1)               ## was last new-var appended, undo
	else:
		result = assign[-1][-1]

					## commander conditions, see section 2
					##
					## these conditions essentially simplify
					## to NAND/OR primitives' clauses,
					## for fanout k=2
	cls = []
	for ai, a in enumerate(assign):
		c, sub = a[-1], a[-2]
		assert(len(sub) <= 2)   ## in case increasing fanout, but
		                        ## forgetting to update something...
		if sub == []:           ## non-hierarchical, pass-through var
			continue

## TODO: top-level variable is just an XOR, or an NAND, depending on
## whether one tolerates 0 or checks for exactly 1 operation.  this
## might be worth documenting in comments; attempt below.
##
##		if (ai+1 >= len(assign)):
##			xconstr, xn, _ = satsolv_xor1(sub[-2], sub[-1])
##			xcomm = f'XXX XOR({sub[-2]},{sub[1]})'
##			for c in xconstr:
##				satsolv_add_constraint1(sat, sSAT_SYM_PREFIX +c,
##							xcomm)
##				xcomm = ''
##		else:

		_, c2 = satsolv_or1(sub[-2], sub[-1], c)
		cls.extend(c2)
				## both sub-variables may not be True
		cls.append( f'-{sub[-2]} -{sub[-1]}' )

	return result, newvar, cls, sat_1ofn_comment(result, vars)


##-----------------------------------------------------------
## add clauses for 1-of-N selections over 'vars'
## returns top-level 'command' variable which is True if and only if 1-of-N
##
## append comments and clauses to respective lists
##
def satsolv_1ofn(sat, vars):
	top, nvars, cls, cmt = satsolv_1n(sat, vars, sat[ 'added_vars' ])

	satsolv_add_vars(sat, nvars)

	sat[ 'added_vars' ] += len(nvars)

	descr = sat_1ofn_comment(top, vars)

	for c in cls:
		satsolv_add_constraint1(sat, sSAT_SYM_PREFIX + c, descr)
		descr = ''

	if satsolv_is_debug():
		for c in cls:
			satsolv_add_constraint1(sat, '', '  ORIG=' +c)

						## force 1-of-N by ensuring
						## commander var is True
	satsolv_add_constraint1(sat, sSAT_SYM_PREFIX + top, descr)

	return top


##-----------------------------------------------------------
## vehicle bitmask intersection: common subset of allowed-vehicle
## bitmasks for two deliveries
##
## returns >0  if there is overlap in possible-vehicle sets for both
##         0   if anything fails (which SNH)
##
def common_vehicles(delvs, d1idx, d2idx):
	if (not delvs) or (d1idx in delvs) or (d2idx in delvs):
		return 0

	mask1 = dict2val(delvs[ d1idx ], 'vehicle_may', -1)
	mask2 = dict2val(delvs[ d2idx ], 'vehicle_may', -1)

	return (mask1 & mask2)


##-----------------------------------------------------------
## cross-delivery dependencies:
##
##   1) enumerate all (delivery, time unit) pairs, which have a possibly
##      overlapping set of vehicles
##
##   2) register variable for each of <dXX tYY v0..vZ> with 0..Z encoding
##      the delivering vehicle (0: no delivery, 1..N: vehicle N, >N: invalid);
##      - D+T times (Z+1) bits, with the number of delivery+units D+T
##
##   3) for each delivery-delivery pair, check minimal distance -> delta(time)
##
##   4) foreach each (delivery, time unit) x2 combination:
##      - if delta(time) > delta(time unit1, time unit2), add prohibition:
##        - v0..vZ for dXXtYY(unit1) MAY NOT be identical to v0..vZ for
##          dXXtYY(unit2), if both values are >0
##
## 'delvs'      is full input list
## 'dts'        stores delivery+time-window crossbar
## 'satvcount'  number of vehicles to allow (+1, all-0, for 'unassigned')
##
## 'conflicts' collects the following form:
##     [ delivery ID(1); time unit(1); delivery ID(2); time unit(2) ]
##
## TODO: delivery-window comparisons are only approximations: we should
## check for maximally lenient deliveries (and filter non-solutions
## iteratively)
##
def satsolv_delv_window_2x_deps(sat, delvs, dist, dts, satvcount):
	dtk = sorted(dts.keys())
	ds  = list(range(len(dtk)))

## caching in an external, d1-only loop has limited utility, since
## distances -> bitmask positions to shift are pair-dependent
##
## in other words, we would not move out everything out of the d1+d2 core
## the bitmask-shift+intersect operations are trivial anyway
##
## note that with only consecutive windows, one could step over all units
## just by a single bitmask but shifting. this is no longer true if
## delivery windows are possible in multiple, non-consecutive units,
## so do not bother with that microoptimization.

				## stores [d1(index), unit, d2(index), unit]
				## tuples which MUST NOT be assigned
				## to the same vehicle
				##
				## units are mapped to 0-based offsets
				## (NOT individual bits of time vector)
	conflict_pairs = []

	for d1i, d2i in itertools.product(ds, ds):    ## all pairs of delv. IDs
		if d1i >= d2i:
			continue

		d1,  d2  = dtk[ d1i ], dtk[ d2i ]
		d1t, d2t = dts[ d1 ][ "t" ], dts[ d2 ][ "t" ]   ## time vectors

		tmax_mask = d1t | d2t     ## limit on checking: max-wid bitmask

## TODO: factor out to centralized deliveries-vs-tables check

		if d1 >= len(dist[ "time" ]):
			raise ValueError("access beyond XY-table dimensions. "
				f"Is this the right lookup table? (X={d1} "
				f"vs. { len(dist[ 'time' ]) })")
					##
		if d2 >= len(dist[ "time" ][ d1 ]):
			raise ValueError("access beyond XY-table dimensions. "
				f"Is this the right lookup table? (Y={d2} "
				f"vs. { len(dist[ 'time' ][ d1 ]) })")

		if (common_vehicles(delvs, d1i, d2i) == 0):
				## TODO: log: delivery pair may not conflict,
				## since they are limited to disjoint sets of 
				## suitable vehicles
				##
			continue

		d12mins =  dist[ "time" ][ d1 ][ d2 ]
		d12mins += vTIME_DELIVER_MIN
				##
				## minimal nr. of minutes between d1 and d2

					## min(traversal), in units
		d12u = int(d12mins +vTIME_UNIT_MINS -1) // vTIME_UNIT_MINS

					## should-not-happen; made explicit
					## TODO: report (table parsing/import
					## SHOULD have caught)
		if d12u < 1:
			continue

					## scan d1 time units: time-dilate
					## in both directions; note where
					## these intercept d2.  those
					## units MUST be prohibited for
					## the same vehicle, since d1->d2 or
					## d2->d1 traversal would violate
					## timing constraint.

					## note that there are some special
					## cases around multi-window
					## deliveries, where dilation may
					## extend into units where delivery
					## may not be scheduled at all

					## all time-vector bits which
					## collide with this (d1, tu),
					## (d1tu < d12u) - ...lower-limit 1...
					##
		d1tu, d2tu = dts[ d1 ][ "tu" ], dts[ d2 ][ "tu" ]
		conflicts = []
			##
			## collects [ delivery1, time1(bit),
			##            delivery2, time2(bit) ] tuples
			## for conflicting pairs

		for u1 in d1tu:
			u1b  = timevecbit2offset(u1)
			allt = 0

				## bits(u1) shifted +-[...conflicting range...]
				## per-bit construction; works
				## regardless of multiple windows
				##
			for shift in range(d12u):
				allt |= (u1b << shift) & tmax_mask
				allt |= (u1b >> shift)

					## units of delivery2 which conflict
					## with this broader 'allt'
					##
			u2clash = list(u  for u in d2tu  if (allt & u))

			for u2b in u2clash:
				u2bit = timevecbit2offset(u2b)

				conflicts.append([d1, u1b, d2, u2bit])

				if not satsolv_is_debug(2):
					continue       ## only diags lines left

				t1s = timevec2wall(u1 )
				t2s = timevec2wall(u2b)
					##
				print(f"## SAT.CONFLICT DELV1={d1}," +
					f"T={ t1s }[{u1b}] DELV2={d2}," +
					f"T={ t2s }[{u2bit}] MIN.TIME.DIFF=" +
					f"{ d12u*vTIME_UNIT_MINS }min")

		if conflicts and satsolv_is_debug():
			print(f"## SAT.COMPAT[{d1},{d2}]: TIME.VEC=" +
				f"[{ delvs[ d1i ][ 'time' ] }]=x{ d1t :x}," +
				f"[{ delvs[ d2i ][ 'time' ] }]=x{ d2t :x}," +
				f"MIN.TIME.DIFF=" +
				f"{ d12u * vTIME_UNIT_MINS }min, " +
				f"CONFLICTS={ len(conflicts) }")

		conflict_pairs.extend(conflicts)

	print(f"## SAT.TOTAL.CONFLICTS={ len(conflict_pairs) }")

			## (1) register all variables, so var-to-int lookups
			##     always succeed
			## (2) raw-register integer-only expressions
			##
			## rationale: post-filtering var-to-int becomes global
			## bottleneck at few hundred thousand constraints

	for c in conflict_pairs:
		satsolv_add_conflict_constraints(sat, c, satvcount)


##-----------------------------------------------------------
## add logical dependencies within each delivery+time unit:
##
##   - dXXtYY <=> collection of dXXtYYvZZ conditions
##
##   - delivery (XX), time unit (YY), binary-encoded vehicle number (ZZ)
##     ZZ with bits v0..v(N-1)
##
##   - dXXtYY  is True if the dXXtYYvZZ bits encode a non-empty vehicle number


##--------------------------------------
## register time-identifying, vehicle-bit-aggregating
##     dXXtYYv0 dXXtYYv1  ->  dXXtYY
##     dXXtZZv0 dXXtZZv0  ->  dXXtZZ
##
## relies on the vehicle-bits encoding being >0 if and only if
## a vehicle is assigned (all-0 means unassigned)
##
def satsolv_delv2time(sat, delv, time_unit, vnr_bits):
	vb = list(vnr_bits)

	tvar  = satsolv_var_name(delv, time_unit=time_unit)
	vvars = list(satsolv_var_name(delv, time_unit=time_unit, vnumber=v)
	                              for v in vb)

	cls, _, _ = satsolv_or('', vvars, result=tvar)

	comm =  f'delivery+time <-> +vehicles: (d={ delv }, t={ time_unit })'
	comm += f' [{tvar} = ({ " OR ".join(vvars) })]'

	for c in cls:
		satsolv_add_constraint1(sat, sSAT_SYM_PREFIX +c, comm)
		comm = ''


##--------------------------------------
## register delivery-identifying, time-independent bits v0..v(N-1)
##     dXXtYYv0 dXXtYYv1
##     dXXtZZv0 dXXtZZv0
##       |        |
##       v        v
##     dXXv0    dXXv1
##
## 'tbits' is bitmask of time units used
##
def satsolv_delv2vehicle(sat, delv, tbits, vnr_bits):
	vb = list(vnr_bits)

	vvars = list(satsolv_var_name(delv, vnumber=v)  for v in vb)
					## naming in v0..v(N-1) identical order

	tvars = list(satsolv_var_name(delv, time_unit=t)  for t in tbits)
					## dXXtYY base IDs

	satsolv_add_vars(sat, vvars)

	for vi, v in enumerate(vb):
		vr = satsolv_var_name(delv, vnumber=v)

						## dXXtYYv0 OR dXXtZZv0 OR ...
						## scans t for identical dXX+v0
## TODO: implicit _var_name construction replicated here:
##
		vconstr, _, vcomm = satsolv_or('',
					(f'{ t }v{vi}'  for t in tvars),
					result = vvars[vi])
		for c in vconstr:
			satsolv_add_constraint1(sat, sSAT_SYM_PREFIX +c, vcomm)
			vcomm = ''


##--------------------------------------
## variables may begin with '-', mapped to negated form (idx<0 in solver input)
##
## TODO: simplified to a form which could be list-comprehended
##
## see also:
##
def satsolv_vars2ints(sat, vars):
	res = []

	for v in vars:
		sgn, val = 1, v

		if val[0] == '-':
			sgn = -1
			val = val[1:]

		res.append(sgn * (sat[ "vars" ].index(val) +1))

	return res


##--------------------------------------
## register constraint on hitting one delivery window for 'delv'
## 'dvars' contains IDs (names) of delivery+unit Booleans
## returns, as a list
##
## all variable names MUST have already been registered to 'sat'
##
def satsolv_add_delvs1(sat, dvars, delv):
	vs   = list(enumerate(dvars))                   ## (idx, variable name)
	didx = delv[ "index" ]

	comm =  f'delivery #{didx} scheduled({delv[ "time" ]}) '
	comm += '(vars=' +(' '.join(dvars)) +')'

	top = satsolv_1ofn(sat, dvars)

	return top


##--------------------------------------
## after timeout, solve the rest through SAT
##
## 'vroute' is already assigned delivery routes (see VRoute)
## 'sat_vehicles' is the nr. of vehicles for remaining/SAT processing
##
def satsolv_rest(sat, delvs, arrivals, vroute, max_vehicles, xy2dist_table):
	if (not use_satsolver()) or sat == None:
		return

			## such as: bypassed backtracking scan
	if not tVID2TIME in arrivals:
		arrivals[ tVID2TIME ] = {}

	if not xy2dist_table:
 		terminate("SAT solver requires XY-to-distance DB")

	vids_assigned = sorted(arrivals[ tVID2TIME ].keys())
		##
	print(sSATCOMMENT +'pre-SAT vehicles assigned ' +
		f'[{ len(vids_assigned) } total]: ' +
		",".join(vids_assigned))

	sat_vehicles = max_vehicles - len(vids_assigned)

	print(sSATCOMMENT +f'max. number of vehicles: { max_vehicles } ' +
		f"({ sat_vehicles :+})")

	if sat_vehicles < 0:
		raise ValueError("too many vehicles already assigned: " +
			f"{ max_vehicles } expected, { len(vids_assigned) } " +
			"already allocated")

	if sat_vehicles <= 0:
		return
				## keep <= comparison, in case above exception
				## picks up additional condition usw.

				## deliveries left for the SAT solver
				##
	sdels = list(sorted(d['index']  for d in delvs
	                    if (not d['index'] in arrivals)))
	if sdels == []:
		print(sSATCOMMENT +"no deliveries left for SAT solver")
		return

	print(sSATCOMMENT +f'deliveries remaining [{ len(sdels) } total]: ' +
		(",".join(str(s) for s in sdels)))

	satvbits   = satsolve_vidx_bits(sat_vehicles)
	satvbitnrs = list(range(satvbits))                  ## 0..N-1, integers
				##
				## width of representation for index(vehicle)
				## incl. an all-0 entry marking
				## 'no vehicle assigned'

	debugmsg(f'## SAT.VEHICLES={ sat_vehicles }', 1)
	debugmsg(f'## SAT.VEHICLE.ID.BITS={ satvbits }', 1)

	if (satvbits > 4):
		raise ValueError("predefined less-than-N SAT forms are " +
				"available up to V=3 vehicle-ID bits")

	satsolv_add_comment(sat, f'using { sat_vehicles } SAT vehicles, ' +
				f'encoded as { satvbits } bits')
	satsolv_add_comment(sat, f'all-00 SAT-vehicle ID: not (yet?) assigned')

	dts = { }                   ## full list of (delivery, time unit) pairs

 	##-----  SAT-pairs list  ---------------------------------------------
	## check for conflicting delivery/time unit/vehicle assignments

	vbitlist = range(satvbits)      ## bit indexes for vehicle IDs
 	                                ## v0..v(N-1) in descriptions

	for sd in sdels:
		d = delvs[sd]                      ## current delivery's struct
		t = d[ "time2vec" ]
				##
		dts[ d[ "index" ] ] = {
			"t":  t,
			"tu": list( timevec2units(t) ),
		}

	for sd in sdels:
		d = delvs[sd]                      ## current delivery's struct
		dvars = []
		didx  = d[ "index" ]

		tu, tbits = dts[ d[ "index" ] ][ "tu" ], []
		for t in tu:
			tb = timevecbit2offset(t)
			tbits.append(tb)

			dvars.append(satsolv_add_delvtime(sat, didx, tb))

			for v in satvbitnrs:
				satsolv_add_delvtime(sat,
				             didx, tb, vnumber=v)

		satsolv_add_delvs1(sat, dvars, d)

		for t in tbits:
			satsolv_delv2time(sat, didx, t, vbitlist)

		satsolv_delv2vehicle(sat, didx, tbits, vbitlist)

	satsolv_delv_window_2x_deps(sat, delvs, xy2dist_table,
	                            dts, sat_vehicles)


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

	sat = satsolv_init0()

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
	print()

	tstart = timediff_log_now(tstart, 'BFD.VEHICLES')

	##-----  tstart is after nr-of-units(BFD) calc  ----------------------

	satvcount  = satsolv_vehicle_count(len(bfds))
				## incl. any additional slack for lower
				## limit inferred from BFD assignment vehicles

## TODO: moved all to satsolv_rest(); no longer used in main flow
##	satvbits   = satsolve_vidx_bits(satvcount)
##	satvbitnrs = list(range(satvbits))                  ## 0..N-1, integers
##				##
##				## width of representation for index(vehicle)
##				## incl. an all-0 entry marking
##				## 'no vehicle assigned'
##
##	if use_satsolver():
##		debugmsg(f'## SAT.VEHICLES={ satvcount }', 1)
##		satsolv_add_comment(sat, f'using { satvcount } vehicles, ' +
##				f'encoded as { satvbits } bits')
##		satsolv_add_comment(sat, f'  all-00: not (yet?) assigned')


	##=====  v1:  ========================================================
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

	##------------------------------
	tmin, tmax = dels[0][ 'MIN_TIME_ALL' ], dels[0][ 'MAX_TIME_ALL' ]
	mins_min, mins_max = dels[0]['MIN_TIME_ALL'], dels[0]['MAX_TIME_ALL']

				## vplans: v.route info, see 'Vehicle Status'
	vplans, done = {}, False
				## done set to True with solution
				##          <0 when exiting

					## arrival times per ID, minutes, for
					## already-fixed deliveries
					## local copy to allow modification
	arrivals = {}
					## TODO: pick up already-fixed entries

	max_mins = timevec2asap(tmax, minutes=True) +vTIME_UNIT_MINS -1
					## not actually reachable

	tbacktrack0 = time.perf_counter()
	tstart = tbacktrack0

	##-----  non-recursive backtracking  ---------------------------------
	## Our implementation tracks a stack of taken+alternative choices,
	## and descends into a hierarchy of that stack in a non-recursive
	## main loop.
	##
	## The main backtrack stack stores only the last choice taken;
	## backtrack-alt (balt[] below) stores the possible choices which
	## were _not_ taken at the same level. The position and path of path
	## descent depend on the current contents of backtrack[]/balt[] ([-1],
	## in Python terms), and a counter marking the number of schedules
	## evaluated for this vehicle, as the loop is entered:
	##
	##    1) backtrack[-1] is non-empty; it contains the last choice
	##       just taken. (We are on our way down the decision tree.)
	##
	##       Action:
	##       Evaluate backtrack[-1] as it has just been taken, descend;
	##       adding a new level to both backtrack[] and balt[].
	##       We extend the current-vehicle delivery plan
	##       with the newly taken choice backtrack[-1].
	##
	##       sanity check: backtrack[-1] MUST be a single entry
	##
	##    2) backtrack[-1] is empty; balt[-1] is not.
	##       We are now evaluating the alternatives of the last-removed
	##       backtrack[-1] entry, checking choices which were
	##       originally listed as alternatives.
	##
	##       Action:
	##       2.1)
	##         Promote first entry of balt[-1] as backtrack[-1];
	##         the search-base entry, which specifies which
	##         deliveries would be reachable, is X,Y and
	##         the leave(ASAP(X,Y)) time from the delivery.
	##         This 'leave()' function is the earliest time,
	##         in minutes, when one can leave (X,Y) after
	##         delivering the previous item.
	##
	##         We replace the just-removed choice with
	##         the alternate target from balt[-1] at
	##         the end of the current-vehicle plan. (By
	##         construction, the last entry must have been
	##         the previously taken choice; we are just
	##         representing the route-to-B-instead-of-A
	##         alternate route here.
	##       2.2)
	##         List all possibilities which can be reached
	##         if leaving (X,Y) not later than leave(X,Y)
	##         within a near-future time window (see vNEXTUNITS),
	##         which would not violate vehicle-packing limits.
	##       2.3)
	##         Sort all choices from (2.2); pick the best-looking
	##         few. (This would, inherited from a BFD background,
	##         would mainly amount to picking those with the
	##         highest primary value; possibly also those very
	##         close to the current delivery.)
	##       2.4)
	##         Assume we take the highest-rated choice from (2.3);
	##         append this to backtrack[].
	##         Take any remaining choices, register them as
	##         alternatives, appending (the list of) them
	##         to balt[].
	##       2.5)
	##         Restart the loop. It will get evaluated in the next (1)
	##         iteration, above, descending into the choice
	##         we have just marked as taken in (2.4)
	##
	##    3) both backtrack[-1] and balt[-1] are empty, and
	##       the nr. of configurations evaluated is >0. We have
	##       just processed the last balt[-1] alternative, and
	##       therefore this entire level of the stack,
	##       and are traversing up.
	##
	##       Action:
	##       Remove both backtrack[-1] and balt[-1], then:
	##       3.1) terminate search if this has been the top
	##         level of the stack.
	##       3.2) remove the backtrack[-2] element, since all its
	##         consequences have just been evaluated, and
	##         restart the loop. It will enter (2) above
	##         or (3) immediately, when it enters the loop
	##         (depending on balt[-2] being empty or not).
	##
	##    4) both backtrack[-1] and balt[-1] are empty (or
	##       no entries at all), and the nr. of configurations
	##       evaluated is 0. We are just entering the loop.
	##
	##       Action:
	##       List all deliveries which may be delivered in the first
	##       vNEXTUNITS time window. Since none of the vehicles have
	##       been scheduled yet, we associate a virtual (X,Y) which is
	##       special-cased: assume all deliveries from this (X,Y)
	##       are reachable (we just turn the required latencies
	##       into earlier departure from the base for the first
	##       delivery of the day/shift/...)
	##
	##       Given a list of earliest-next-units deliveries, just as if
	##       they had been output by (2.2), and enter (2.3) above.
	##
	## We expect to detect the absence of configurations entirely
	## before attempting config enumeration, so config >0 vs. ==0
	## is unambigous.
	##-----  /non-recursive backtracking  --------------------------------

	nr_routes_all = 0
					## total nr. of configurations tested,
					## for all vehicles

					## brute-force plan generation for each
					## vehicle, based on BFD approximation
	while (done == False):
		t, nr_routes = tmin, 0
					## nr. of routes checked (this vehicle)

		now_min = timevec2asap(t, minutes=True)
					## time(current vehicle), in minutes
					##
					## backtracking may roll this back
					## to a past value

		vid   = virtual_vehicle2id( len(vplans) )
		vcost = vehicle_cost0()          ## current vehicle, cost total

		vbit = 1 << len(vplans)
			## TODO: static vehicle-to-[something] assignment

		vplans[ vid ] = vcost

		debugmsg(f'## PLAN.VEH.NR={ len(vplans) }', 2,
		         type=vTRC_SCHED)

		##-----  set up all initial vars; may terminate  -------------
		if ('PACK_N_ROUTE_SKIP' in os.environ):
			break            ## TODO: proper setup for early skip

				## redundant copies of vplans[] fields
		x, y = None, None

				## best seen solution in current search
				## [ sum(primary); [ ...delivery list... ] ]
		best = None

		backtrack, btrack_alt = [], []
				## save yet-unexplored alternatives, in
	                        ## scanning order. emerging from backtrack
	                        ## sets first delivery, then descends.

		do_backtrack = False
				## set to True and 'continue' from loop below
				## to force backtrack (just below loop)

		tstart = time.perf_counter()
		tstart_this_vehicle = tstart

				## scan yet-unassigned deliveries which
				## may be started in [t .. t+vNEXTUNITS)

		while (now_min < max_mins):
				## keep conditions below redundant, not
				## stack them: without factoring out,
				## we would be too deeply nested.

			print(f"## ARRIVALS.RESVD.COUNT=[{ len(arrivals) }]")

			if are_in_timeout(tstart):
				print("TIMED.OUT")
				report_plan(vcost, vid, marker='?')
				print("/TIMED.OUT")

						## solve the rest through SAT
				satsolv_rest(sat, dels, arrivals, vcost,
				             satvcount, xy2dist_table)
				satsolv_report(sat)
				sys.exit(0)

			show_backtrack(backtrack, btrack_alt)
			debugmsg(f'## MAIN.LOOP.NOW={ minute2wall(now_min) }',
			         1, type=vTRC_SCHED | vTRC_FLOW)

			assert_backtrack_stacks(backtrack, btrack_alt)

			##-----  backtrack paths:  ---------------------------

				## see case numbers in flow description above
				##
				## loop restart/terminate steps are highlighted
				## to simplify control flow tracing

			if (backtrack == []) and (nr_routes > 0):
					## (3.1), checked all routes; exit

				debugmsg('## MAIN.LOOP.END', 1, type=vTRC_FLOW)
				debugmsg('## MAIN.LOOP.VEH.ROUTES.TOTAL' +
				         f'={ nr_routes }',
				         3, type=vTRC_FLOW)
				break
				##-----  terminate loop  ---------------------

			next = None
						## 'next' set to non-None
						## if it is a known next move
						## first candidate otherwise

						## no past history, empty
						## stack: pick up first entries
						##
						## entering loop for the
						## first time               (4)
						##
			if (backtrack == []) and (nr_routes == 0):
				debugmsg('## MAIN.LOOP.ENTER(FIRST)',
				         2, type=vTRC_FLOW)
				pass            ## (4) -> fall through to (2.2)

			elif backtrack[-1] != []:    ## choice was taken
			                             ## (1) -> (2.2)
				next = backtrack[-1]
				debugmsg('## MAIN.LOOP.CHOICE(STACK)',
				         1, type=vTRC_FLOW)
						##

				nroute = vroute2normalized(vcost)
				debugmsg(f'## MAIN.NEW.ROUTE.NORM={ nroute }',
				         2, type=vTRC_FLOW)
				vcost[ 'checked' ][ nroute ] = 1

			elif (btrack_alt[-1] != []):
						## choice emptied, alternates
						## still exist. Promote first
						## alternate as next move,
						## then process it (as 2.1)
						##
				debugmsg('## MAIN.LOOP.ALTERNATE(1-of-' +
				         f'{ len(btrack_alt[-1]) })',
				         1, type=vTRC_FLOW)
					##
				next = btrack_alt[-1].pop(0)
				backtrack[-1] = next

			else:            ## processed both main and alternates,
			                 ## backtrack to previous choice
			                 ## (above this one in stack)       (3)
				backtrack.pop(-1)
				btrack_alt.pop(-1)
				vroute_backtrack1(vcost, dels, arrivals)

				debugmsg('## MAIN.LOOP.BACKTRACK.UP',
				         1, type=vTRC_FLOW | vTRC_STACK)
				continue
				##-----  restart loop  -----------------------

			##-----  administer new entries (2.1, 2.2)  ----------
			## (1) one has been picked from backtrack stack;
			##     it is in 'next' if non-None; that entry
			##     has already been removed from stack.
			##     find candidates reachable after delivering
			##     the 'next' entry.
			## (2) find initial candidates if 'next' is None

			if next:
				pass

			mr = delivery_candidates(vcost, dels, arrivals,
			                         vbit, vid, now_min)

			##-----  branch-trim heuristics would come here  -----

## TODO: proper branch-trim heuristic!
## in the beginning, discard things much lighter than first assignment
## cuts down branching of early searches

## heuristic: take heaviest few possibilities
## reasonable, since BFD would prefer those anyway

			mr = mr[ : vBFD_MAX_CANDITATES ]

			##-----  /branch-trim heuristics  --------------------

			debugmsg(f'## SCHED.FINAL.CANDIDATES.COUNT={ len(mr) }',
			         1, type=vTRC_SCHED)
			debugmsg('## SCHED.FINAL.CANDIDATES=' +
			         ','.join(mayreach2str(m) for m in mr),
			         1, type=vTRC_SCHED)

			if mr == []:           ## no candidates left? backtrack
				if backtrack != []:
## TODO: factor out recurring theme 'pick N before last if present'
					now_min = backtrack[-1][4]
## TODO: symbolic indexes of array structs
						## time before last delivery,
						## which is now rolled back
					backtrack[ -1 ] = []       ## processed
				else:
					now_min = 1   ## arbitrary valid time
					              ## loop restart terminates

				continue
					##-----  end of search, backtrack
## TODO: delay until a later delivery window would come here

			nr_routes += 1
					## accept 1st candidate
					## store others as alternates
			id, sum1, _, asap, now_min = mr.pop(0)

			backtrack.append([ id, sum1, vid, asap, now_min ])
			btrack_alt.append(mr)
					##
					## descend into current choice
					## mark alternatives to explore
					## after return from backtrack below

			now_min = vehicle2xy_minimal_min(vcost, arrivals,
			                     vid, id, asap, dels)
			register_arrival(arrivals, id, vid, asap)

					## did this delivery get 'close enough'
					## to a solution?
## TODO: wrapper to pick assigned vs. unassigned
## currently, nr-assigned is unused since limit is fixed
##
			max1_current = current_anneal_limit(len(arrivals),
						len(deliveries))

			##---  terminate if solution got 'close enough'  -----
			## check for under-limit is redundant
			##
			if ((vcost["primary"] >= max1_current) and
			    (vcost["primary"] <= MAX1)):
				best = maybe_register_best(best, vcost,
				             arrivals)   ## just add newest one

				print(f"## QUALITY.CURR={ max1_current }")
				print(f"## SUM.PRIMARY={ vcost['primary'] }")
				print("## sum(primary) over current quality " +
					"limit, ACCEPTING AS ROUTE")
				done = True
				break

			best0 = best
			best  = maybe_register_best(best, vcost, arrivals)
			if (best != best0):
## ...log here...
				sys.stdout.flush()

			continue
## RRR
##============================================================================

			##-----  backtrack:  ---------------------------------
			if do_backtrack:
				if backtrack == []:
					tstart = timediff_log_now(
						tstart_this_vehicle,
						'BFD.ASSIGN.CURRENT')
					break        ## nothing left to explore

				print(f"## BACKTRACKING [{ len(backtrack) }] "
				      f"level/s, {nr_routes} config/s checked")

## TODO: proper debug-control
				if debug_is_active(1) and False:
					show_backtrack(backtrack, btrack_alt)

						## un-assign last assignment
						##
				prev = backtrack.pop(-1)
				debugmsg(f'## BACKTRACK.UNDO={ prev }',
				         1, type=vTRC_STACK)

					## sanity check: delivery just
					## removed MUST be marked as assigned:
					## was marked as such when originally
					## descending
					##
				rmid = prev[0]      ## id(just removed delivery)
				if not rmid in arrivals:
					raise ValueError(f"backtracking with "
						"incorrectly registered " +
					        f"delivery ({ prev[0] })")

				del(arrivals[ rmid ])
					##
					## backtracked entry MUST also be
					## last delivery in vehicle plan
					##
				vp_delv = vplans[ vid ][ 'stops' ][-1][1]
				if rmid != vp_delv:
					raise ValueError("backtrack stack " +
						"disagrees with route list " +
						f"(delv={ prev[0] }, " +
						f"list={ vp_delv })")
					##
					## also remove last segment from cost
					##
				rm1 = dels[ rmid ][ 'primary'   ]
				rm2 = dels[ rmid ][ 'secondary' ]
## TODO: this is a 'check that we are removing delivery X, which must be
## at the end of the current schedule' condition; to be centralized

					## some sanity checks: load
					## accounting is correct
					##
				if vcost[ "primary" ] < rm1:
					raise ValueError("backtrack stack " +
						"weight inconsistent " +
						f"(delv={ prev[0] }, " +
						f"-=PRIMARY={ rm1 })")
					##
				if vcost[ "secondary" ] < rm2:
					raise ValueError("backtrack stack " +
						"weight inconsistent " +
						f"(delv={ prev[0] }, " +
						f"-=SECONDARY={ rm2 })")

## TODO: this part of replacement is essentially a 'swap delivery X to Y'
## operation. if we factor it out, it simplifies subsequent
## delivery-swapping checks

## TODO: elem-count conditional
## XXX roll back vehicle
					## sanity check: last stop MUST be
					## identical to what we are removing
					##
				if (vplans[ vid ][ 'stops' ] == []):
					raise ValueError("backtrack stack " +
						"stop count inconsistent " +
						f"(delv={ prev[0] })")

## TODO: factor out these +- adjustments
				vcost[ "distances" ].pop(-1)
				vcost[ "d_minutes" ].pop(-1)
				vcost[ "arrivals"  ].pop(-1)
				vcost[ "primary"   ] -= rm1
				vcost[ "secondary" ] -= rm2

				if (len(vcost[ 'stops' ]) >= 2):
					debugmsg('## BACKTRACK.V.STOPS.LAST=' +
					   f'(..{ vcost[ "stops" ][-2:] })',
				       	   1, type=vTRC_STACK)

				ldel = vplans[ vid ][ 'stops' ].pop(-1)
					## remove last delivery from list(stops)
					##
				if (ldel[1] != rmid):
					raise ValueError("backtrack stack " +
					    "stops inconsistent " +
					    f"(delv={prev[0]}, d.id={rmid}, "+
					    f"stop id={ ldel[1] })")

					## roll back now_min to leave(last.del)
					## or 'no past time', depending on
					## whether backtracked to empty list
					##
				if vcost[ "stops" ]:
					now_min =  vcost[ "stops" ][-1][0]
					now_min += vTIME_DELIVER_MIN
				else:
					now_min = tmin
				t = minute2timevec(now_min)

					## (1) if no alternatives left, ascend
## TODO: protection against [-1] above?
				if (btrack_alt[-1] == []):
					btrack_alt.pop(-1)
					continue

					## (2) if there are alternatives,
					## promote next one as taken, continue
					## -> nr. of backtrack levels unchanged
## TODO: check that [-1] -> 'next' traversal is possible
					##
				next = btrack_alt[-1].pop(0)
				backtrack.append([ id, 666, vid, asap,
				                   now_min ])

## [198, 901741130, 'VEHICLE00', 30, 0]
## XXX format
					##
				debugmsg(f'## BACKTRACK.TAKE.ALTERNATE={next}',
				         1, type=vTRC_STACK)

					## sanity check: delivery just removed
					## MUST NOT be marked as assigned
					##
				if next[0] in arrivals:
					raise ValueError(f"backtracking with "
						"incorrectly registered " +
					        f"alternate ({ next[0] })")

					## sanity check: next-possible delivery
					## MUST NOT overload vehicle;
					## would have been filtered out
					## during alt-candidate search
					##
				if (next[1] + vcost['primary'] > MAX1):
					raise ValueError(f"backtrack did not "
						"filter out overpacked " +
					        f"delivery (+{ next[1] })")

				id, _, asap, now_min = next

					## advance vehicle to now-taken
					## alternative delivery
					##
				now_min = vehicle2xy_minimal_min(vcost,
					arrivals, vid, id, asap, dels)
				t = minute2timevec(now_min)

			do_backtrack = False
			##-----  /backtrack  ---------------------------------

			debugmsg('## MAIN.LOOP, AFTER BACKTRACK',
			         3, type=vTRC_FLOW)

##			show_backtrack(backtrack, btrack_alt)

			## find feasible candidates, assign them
			me = t +vTIME_UNIT_MINS * vNEXTUNITS -1
			debugmsg(f'## T.NOW={ minute2wall(now_min) }' +
				f'({ now_min })')
			debugmsg(f'## T.MAX.NOW={ minute2wall(me) }({ me })')
				##
			t0 = timevec2asap(t, minutes=True)
			te = t0 + vTIME_UNIT_MINS * vNEXTUNITS -1
			tmask = (t << vNEXTUNITS) -t
						## immediate-future time units,
						## where we consider deliveries

						## minute of previous arrival,
						## incl. any previous-delivery
						## overhead
						##
			if (x == None) and (vcost['stops'] == []):
				arrived = now_min      ## newly started vehicle
			else:
				arrived =  vcost[ 'stops' ][-1][0]
				arrived += vTIME_DELIVER_MIN
					##
				x, y = vcost[ 'stops' ][-1][ -2: ]
				x, y = float(x), float(y)

## TODO: symbolic const for [0] -> index-of-minutes

			debugmsg(f'## T.WINDOW={ minute2wall(t0) }..' +
				 f'{ minute2wall(te) }', 1)
			debugmsg(f'## T.WINDOW.X=x{ tmask :x}', 1)

					## find which deliveries:
					## (1) may be delivered in immediate
					##     future (vNEXTUNITS)
					## (2) are not yet assigned
					## (3) may be assigned to  this vehicle
					## (4) do not overload vehicle
					##
					## also, checked subsequently,
					## (5) vehicle may actually
					##     get there within (1)
					##
			ds = list(d  for d in dels
				if ((tmask & d[ 'time2vec' ])     and    ## (1)
				    (not d["index"] in arrivals)  and    ## (2)
				    (vbit & d[ 'vehicle_may' ])))        ## (3)

					## 'may reach'
					## (index, primary) tuples
					##
			mr = sorted(([ d["index"], d["primary" ], ]
		 	       for d in ds
			       if (d["primary"]+vcost["primary"] <= MAX1))) #(4)

			mr = sorted(mr, key=operator.itemgetter(1),
			            reverse=True)
					## in decreasing primary order

			## note: not yet looked at XY-to-XY latencies

## TODO: filter directly using xy2asap_minute(), which is now
## replicated below
## TODO: formalized representation of intentionally skipped deliveries

			debugmsg('## SCHED.NOW.CANDIDATES0=' +
			         ','.join(mayreach2str(m) for m in mr),
			         2, type=vTRC_SCHED)

## TODO: special-case initial route from base to first (X,Y)
##       needs preferred/fixed/etc. vehicle-to-base assignment

					## turn [ idx, primary ] to
					## [ index, primary, ASAP(min) ]
					## tuples
			if x != None:
				mrn = []
				for di, add in mr:
					twindow = tmask & dels[di]['time2vec']
					dx, dy = dels[di]['x'], dels[di]['y']

					asap = xy2asap_minute(x, y, dx, dy,
					               arrived, twindow)

						## (5) vehicle may actually
						##     get there to hit (1)
						## see conditions above
						##
					if asap != None:
						mrn.append([ di, add, asap,
						             now_min, ])
			else:
						## starting new vehicle: can
						## reach start of window
				mrn = []
				for di, add in mr:
					twindow = tmask & dels[di]['time2vec']

					mrn.append([ di, add,
					    timevec2asap(twindow, minutes=True),
					    now_min,
					])
			mr = mrn
## TODO: check for return-to-base as an option

			##-----  branch-trim heuristics would come here  -----
## TODO: proper branch-trim heuristic!
## in the beginning, discard things much lighter than first assignment
## cuts down branching of early searches

## heuristic: take heaviest few possibilities
## reasonable, since BFD would prefer those anyway

			mr = mr[ : vBFD_MAX_CANDITATES ]

			##-----  /branch-trim heuristics  --------------------

						## no candidates?
			if mr == []:
				if no_feasible_future_delv(dels, vcost,
				               arrivals, now_min, maxu):
					assert(0)
## TODO: other terminate-and-backtrack conditions

				##-----  consider current state as solution

						## nothing visible in
						## current prediction window
						## we still have time to check
						##
				if (t < tmax) and (now_min < max_mins):
					t <<= vNEXTUNITS
					tstr = minute2wall(timevec2asap(t,
							       minutes=True))
					debugmsg('## SCHED.DELAY.TO=' +
						 f'{ tstr }',
						 1, type=vTRC_SCHED)
					if not shown_btrack:
						show_backtrack(backtrack,
						               btrack_alt)
					continue

				## backtrack: nothing else left
				assert(0)

			debugmsg(f"## BACKTRACK.STACK={ backtrack }",
			         2, type=vTRC_SCHED | vTRC_STACK)
			if btrack_alt:
				debugmsg("## BACKTRACK.CURR.ALTERNATES=[" +
					",".join(mayreach2str(b)
				                 for b in btrack_alt[-1]) +"]",
				         2, type=vTRC_SCHED)

## TODO: backtrack-alternatives stack: pretty print etc. in one spot
			debugmsg('## SCHED.NOW.CANDIDATES=' +
			         ','.join(mayreach2str(m) for m in mr),
			         2, type=vTRC_SCHED)

			debugmsg('## MAIN.LOOP, AFTER NEW CANDIDATES',
			       	 3, type=vTRC_FLOW)

			if mrn == []:
				assert(0)
						## nothing to process; MUST
						## have been processed above
			descend = False

			##-----  descend into each option in turn
			for cidx, choice in enumerate(mrn):
				id, pr, asap = choice

## TODO: filtered above: delivery is already scheduled+arrived
## better check to avoid redundancy
				if id in arrivals:
					continue

				asap = vehicle2xy_minimal_min(vcost, arrivals,
						vid, id, asap, dels)
				if asap == None:
					continue            ## can not reach in
					                    ## reasonable time

				now_min = asap +vTIME_DELIVER_MIN
				t = minute2timevec(now_min)
					##
				backtrack.append([ id, asap, vid, now_min ])
				btrack_alt.append(mrn[ cidx+1: ])
					##
					## descend into current choice
					## mark alternatives to explore
					## after return from backtrack below

				register_arrival(arrivals, id, vid, asap)
				best = maybe_register_best(best, vcost,
				                           arrivals)
				descend = True
				break

			if descend:
				continue

				## no pending delivery in immediate future
				## shift window to next band (since nothing
				## will be visible in current one)

## TODO: there is another instance above; factor out
			if (t < tmax):
				t <<= vNEXTUNITS
				tstr = minute2wall(timevec2asap(t,
				                           minutes=True))
				debugmsg('## SCHED.SHIFT.TO=' +
				         f'{ tstr }',
				         1, type=vTRC_SCHED)
				continue

				## out of options
				## backtrack? (check exact fail condition)
			assert(0)

		##-----  current vehicle terminated  -------------------------
		## administer it, check for rest

		timediff_log_now(tstart_this_vehicle, 'BFD.ASSIGN.CURR')

				## since we backtracked to the top, 'arrivals'
				## has removed all deliveries;
				## register them for best solution
				##
		if best == None:
			raise ValueError("did not find a solution?")

		register_best2global(arrivals, best, vid)

		nr_routes_all += nr_routes

		debugmsg('## MAIN.LOOP.ROUTES.TOTAL' +
		         f'={ nr_routes_all }(+{ nr_routes })',
		         2, type=vTRC_FLOW)

		debugmsg(f'## /VEHICLE.ASSIGN(ID={ vid })')
		debugmsg(f'## DELIVERIES ASSIGNED: { len(arrivals) }/' +
			f'{ len(dels) }')

		tend = time.perf_counter()
		debugmsg(f'## time(VEH={ vid })={ timediff_str(tstart, tend) }',
		         lvl=1, type=vTRC_TIME)
		tstart = tend
		print()

		done   = False

					## termination condition: 3sec
		if are_in_timeout(tstart):
			print("TIMED.OUT")
			break

	if ('PACK_N_ROUTE_SKIP' in os.environ):

						## solve the rest through SAT
		satsolv_rest(sat, dels, arrivals, vcost,
		             satvcount, xy2dist_table)
		satsolv_report(sat)
		sys.exit(0)

	tstart = timediff_log_now(tbacktrack0,
		'BFD.ASSIGN.ALL'  if done  else 'BFD.ASSIGN.PARTIAL')
	print('')
	##=====  /v1  ========================================================

	sys.exit(0)

		## got initial time plan, covering some subset of vehicles
		## turn unassigned deliveries and vehicles into SAT solver

 	##-----  SAT-pairs list  ---------------------------------------------
 				## full list of (delivery, time unit) pairs
	dts = { }
	sys.exit(0)

	##-----  store delivery/time variables
	if use_satsolver():
		if not xy2dist_table:
			terminate("SAT solver requires XY-to-distance DB")

		for d in dels:
##		for d in (d  for d in dels  if ):
			t = d[ "time2vec" ]
					##
			dts[ d[ "index" ] ] = {
				"t":  t,
				"tu": list( timevec2units(t) ),
			}

		vbitlist = range(satvbits)      ## bit indexes for vehicle IDs
		                                ## v0..v(N-1) in descriptions


##		for d in (d  for d in dels :

## 			dvars = []
## 			didx  = d[ "index" ]
## ## TODO: retrieve from above table, now that we populate it
##
## 				## register dXXtYY and dXXtYYvZZ
## 				##   - delivery XX, time unit YY
## 				##   - delivery XX, time unit YY,
## 				##     vehicle-ID ZZ
## 				## 'vehicle ZZ' covers bits, not counters
## 				## (binary-encoded index of vehicle assigned)
## 				##
## 				## with 4 vehicles, v0 and v1; variables:
## 				##     dXX-tYY-v0
## 				##     dXX-tYY-v1
## 				## combinations of v0+v1 used to count
## 				## (1-based) delivery index
##
## 			tu, tbits = dts[ d[ "index" ] ][ "tu" ], []
##
## 			for t in tu:
## 				tb = timevecbit2offset(t)
## 				tbits.append(tb)
##
## 				dvars.append(satsolv_add_delvtime(sat,
## 				             didx, tb))
##
## 				for v in satvbitnrs:
## 					satsolv_add_delvtime(sat,
## 					             didx, tb, vnumber=v)
##
## 			satsolv_add_delvs1(sat, dvars, d)
##
## 			for t in tbits:
## 				satsolv_delv2time(sat, didx, t, vbitlist)
##
## 			satsolv_delv2vehicle(sat, didx, tbits, vbitlist)
##
## 		satsolv_delv_window_2x_deps(sat, dels, xy2dist_table,
## 		                            dts, satvcount)
##
## 	del(dts)
## 	##-----  /SAT-pairs list  --------------------------------------------

	satsolv_report(sat)

	sys.exit(0)


## 	##-----  v2:  --------------------------------------------------------
##
## 				## pick "reasonably spaced" start times for
## 				## all deliveries
## 	dels = copy.deepcopy(aux)
##
## 	tstart = time.perf_counter()
## 	starttimes(dels)
## 	tend = time.perf_counter()
## 		##
## 	debugmsg(f'## time(START.TIMES)={ timediff_str(tstart, tend) }',
## 	         lvl=2, type=vTRC_TIME)
## 	tstart = tend
## 	##-----  tstart is after initial delivery assignments  ---------------
##
##
## 	tmin, tmax = dels[0][ 'MIN_TIME_ALL' ], dels[0][ 'MAX_TIME_ALL' ]
## 	t = tmin
##
## 	backtrack  = []         ## assigned in each turn
## 	btrack_alt = []         ## alternates to those assigned in each turn
## 	                        ## MUST evolve in matched pairs
##
## 	avail   = len(vpos)     ## number of new vehicles one may assign
## 	delayed = {}            ## anything pushed back in current schedule
##
## 	vpos0 = copy.deepcopy(vpos)
##
## 				## enumerate delivery windows (bits in mask)
## 				## in chronological order
## 	while (t <= tmax):
## 		assert(len(backtrack) == len(btrack_alt))      ## matched pairs
##
## 		t0 = timevec2asap(t, minutes=True)
## 		te = t0 + vTIME_UNIT_MINS -1
## 		tunit = t.bit_length()-1               ## 0-based, from tmin...
## 		t += t             ## current t is t/2; allow simple continue
##
## 		debugmsg(f'## T.WINDOW={ minute2wall(t0) }..' +
## 			 f'{ minute2wall(te) }', 1)
##
## 		##---  enumerate all possible (delivery, vehicle) pairs  -----
## 		## (1) 'new vehicle' assignment appear, once, if new vehicles
## 		##     may still be added/assigned
## 		## (2) delay listed as 'vehicle' if still possible
##
## 						## which deliveries have
## 						## been pre-scheduled here?
## 		ds = list(d  for d in dels
## 			if (('window' in d) and (t & d['window']) and
## 			    (not is_delivery_frozen(d))))
##
## 		didxs = list(sorted(d[ "index" ] for d in (ds)))
##
## 					## which one of the delayed deliveries
## 					## may be considered in this time unit?
## 					##
## 		ddelay_now = list(d  for d in delayed.keys()
## 		                  if ((t & dels[d][ 'window' ] and
## 		                      not is_delivery_frozen(dels[d]))))
## 					##
## 		ddelay_now = list(sorted(ddelay_now))
##
## 		if debug_is_active(3, vTRC_SCHED | vTRC_STACK):
## 			print('## BACKTRACK.TAKEN ', backtrack)
## 			print('## BACKTRACK.ALT   ', btrack_alt)
## 					## backtrack stack at entry
##
## 		if debug_is_active(2, vTRC_SCHED):
## 			print('## SCHED.INIT0.NOW    ', didxs)
## 			if ddelay_now:
## 				print('## +BACKTRACK.DELAYED ',
## 				      ",".join(str(di)
## 				          for di in sorted(ddelay_now)))
##
## 		didxs.extend(ddelay_now)
## 		didxs = list(sorted(didxs))   ## anything possibly starting now
##
## 		if debug_is_active(2, vTRC_SCHED):
## 			print('## SCHED.NOW.CHECK    ', didxs)
##
## 				## plus anything delayed to now, IF they
## 				## may be delivered in this window
##
## 		debugmsg(f'## T.START0.COUNT={ len(didxs) }', 1,
## 		         type=vTRC_SCHED)
## 		if ds:
## 			debugmsg('## T.DELVS.NOW=' +
## 				f'{ ",".join(str(di)  for di in didxs) }', 1)
##
## 				## time assignments in current round
## 				## nr. of possible pairs (total)
## 				## does this combination break/backtrack?
## 		curr, pairs, btrack = {}, 0, False
## 				##
## 				## curr {
## 				##	delivery: [[veh.ID, ASAP], ...]
## 				## }
## 				## collects only already running vehicles
## 				## new vehicle assignments or delays handled
## 				## differently
## 				##
## 				## pairs is total nr. of non-special
## 				## vehicle assignments
## 				##
## 		spec_sched = {} ## number of special schedule options,
## 				## indexed by delivery index
##
## 				## delivery indexes which may be delayed
## 				## or may be assigned a new vehicle,
## 				## respectively
## 		may_delay, may_assign_new = {}, {}
## 				##
## 				## note: redundant; consolidate, see
## 				## vDELAY_DELIVERY and vNEW_VEHICLE
##
## 		ds = list(sorted(ds, key=del_unit2sort))
## 		for d in ds:
## 			didx     = d[ 'index' ]
## 			x, y     = d['x'], d['y']
## 			new_load = [ d['primary'], d['secondary'] ]
## 			                 ## assigning new vehicle or delaying
##
## 			debugmsg(f'## T.DELV.IDX={ didx }', 1)
## 			debugmsg(f'## T.DELV.WINDOW={ d["time"] }', 1)
## 			debugmsg(f'## T.DELV.XY={ x },{ y }', 2,
## 			         type=vTRC_MAP)
##
## 			spec_sched[ didx ] = 0
##
## 			vs   = vehicle_may_reach(x, y, t, vpos, xy2d, d,
## 			                         assign_new=False)
## 			vids = vehicles_which_may_deliver(new_load, vs,
## 			                                  vpos, minute0=t0)
## 			curr[ didx ] = vids
## 			if (avail > 0):
## 				may_assign_new[ didx ] = 1
## 				spec_sched[ didx ] += 1
##
## 			if has_time_after(d, t):
## 				may_delay[ didx ] = 1
## 				spec_sched[ didx ] += 1
## 				curr[ didx ].append([ vDELAY_DELIVERY, t0, ])
##
## 				## categorize all possibilities; pick option
## 				## to descend into.  split option tuples into
## 				## (1) assigned (2) alternate groups; first
## 				## one is assigned, second one will be picked
## 				## up when backtracking
## 				##
## 				## each delivery has only one option assigned
## 				## to it; if out of options, backtrack.
##
## 			if (vids == []) and (spec_sched[didx] == 0):
## 				btrack = True
## 				break
##
## 			pairs += len(curr[ didx ]) + spec_sched[didx]
##
## 		if btrack:
## 			assert(0)
## 			pass
##
## 		if debug_is_active(1, vTRC_SCHED):
## 			print('## DELV.SCHED.TUPLES[time.w=' +
## 				f'{ tunit }].COUNT={ pairs }')
## 			print(f'## VEH.AVAIL={ avail }')
##
## 			for d in sorted(curr.keys()):
## 				dstr = ",".join(delvtuple2str(v, asap)
## 				                for v, asap in curr[d])
## 					##
## 				print(f'## DELV[{ d }]={ dstr }')
##
## 		if curr == {}:     ## no delivery to schedule in this time unit
## 			backtrack.append([])
## 			btrack_alt.append([])
## 			continue
## 				## already backtracked above w/o valid schedule
##
## 					##------------------------------------
## 					## nr. of options for each delivery
## 					## incl. delay or new vehicles
## 		nro = {}
## 		for d in curr.keys():
## 			nro[d] =  len(curr[d]) + (1 if (d in may_delay) else 0)
## 			nro[d] += (1  if (d in may_assign_new)  else 0)
##
## 		assert(0 < min(nro.values()))
## 					##
## 					## if delivery exists with no options,
## 					## MUST have already backtracked above
##
## 		##----------------------------------------------------
## 		## split [delivery: vehicle, ASAP] tuples' list
## 		## to 'taken', 'not taken' list of options
## 		##
## 		## one option per delivery; rest go to
## 		## alternates for backtrack-alternate stack
##
##
## 		##====================================================
## 		## this is where choice-enumeration magic happens
## 		##
## 		## collect all additions to 'now' and 'alt', then append
## 		## to backtrack[]/btrack_alt[]
## 		## entries are [ d.index, vehicle ID, ASAP, ]
## 		##
## 		## we do not currently organize that way, but this two-step
## 		## build would allow context-aware sorting of
## 		## currently-selected assignments
## 		##
## 		now, alt = [], []
##
## 				## (1) index of deliveries with (A) only one
## 				##     option, excluding new vehicles (which
## 				##     are capacity-limited, and counted below)
## 				## assign these unconditionally
## 				##
## 		didxs_1choice = list(sorted(di  for di in curr.keys()
## 		                     if ((nro[di] == 1) and              ## (A)
## 		                         (not di in may_assign_new))))
##
## 		if didxs_1choice and debug_is_active(2, vTRC_SCHED):
## 			print('## DELV.FIXED=', didxs_1choice)
## 							## TODO: pretty-print
##
## 		for di in didxs_1choice:
## 			if di in may_delay:
## 				now.extend([ di, vDELAY_DELIVERY, minute0, ])
## 			else:
## 				now.extend([ di, curr[di][0][0],
## 				             curr[di][0][1], ])
##
## 				## (2) trim current-index list to anything
## 				##     remaining with multiple choices
## 				##
## 		didxs = list(di  for di in didxs  if (not di in didxs_1choice))
##
## 				## (3) enumerate delivery-vehicle assignments
## 				##     considers number of available ones
## 				##
## 		vas = list(vehicle_assignments(didxs, curr, t0, avail,
## 		                               may_delay))
##
## 				## are there enough unassigned vehicles
## 				## to try all the single-option ones?
## 				##
## 				## if not, we need to backtrack: previous
## 				## choices do not leave us enough unassigned
## 				## vehicles which SHOULD be assigned now
##
## 				## (3) choices (tuples) for each
## 				##     still-unassigned delivery
## 				##
## 				## TODO: 'allow new vehicle' strategy
## 		for di in didxs:
## 			v, asap = curr[di].pop(0)
##
## #			if (di in may_assign_new):
## #				avail -= 1
##
## 			now.append([ di, v, asap, ])
## #			if (v == vDELAY_DELIVERY):
## #				maydelay[di] = 1
##
## 			for v, asap in curr[di]:
## 				alt.append([ di, v, asap, ])
##
## 			continue   ## XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
##
## 			vchoices = list([v, asap]  for v,asap in curr[di]
## 			                if not is_special_vehicle(v))
## 				##
## 				## choices which involve actual vehicles
## 				##
## 				## try them in increasing distance order,
## 				## which SHOULD be the case by now
## 				## (after vehicle_may_reach())
##
## 				## no newly assigned vehicle would
## 				## arrive later than an existing one,
## 				## since we assume the former will be
## 				## started early enough to hit the
## 				## start of current time unit.
## 				##
## 				## note: a vehicle MAY also arrive
## 				## immediately, f.ex. if its earliest
## 				## arrival would have been in a preceding
## 				## time unit, when this delivery would not
## 				## have been possible.
##
## 			while True:         ## first suitable case breaks
## 				newv = []
## 				if di in may_assign_new:
## 					newv = [ di, vNEW_VEHICLE,
## 					         timevec2asap(t, minutes=True),
## 					]
##
## 				if asap:
## 					if newv:
## 						now.append(newv)
##
## 					elif vchoices:
## 						va = vchoices.pop(0)
## 						now.append([ di, va[0], va[1], ])
##
## 					if vchoices:
## 						alt.extend([ di, v, asap, ]
## 						       for v,asap in vchoices)
## 					break
##
## 				if alap:
## 					vchoices = list(reversed(vchoices,
## 				                key=operator.itemgetter(2)))
## 					##
## 					## prefer later-to-earlier deliveries
## 					## input list was chronological
##
## TODO: recurring primitive, factor out
## (will be simplified once this is simplified to a Karnaugh map)
##
## 					if vchoices:
## 						va = vchoices.pop(0)
## 						now.append([ di, va[0], va[1], ])
## 						alt.extend([ di, v, asap, ]
## 						       for v,asap in vchoices)
## 					break
##
## 				if newv:
## 					now.append(newv)
##
## 				if vchoices:
## 					va = vchoices.pop(0)
## 					now.append([ di, va[0], va[1], ])
## 					alt.extend([ di, v, asap, ]
## 					           for v,asap in vchoices)
##
## 				break
## 			##-----  end of assign-one-delivery loop
##
## 		newvhs = list(di  for di in didxs_1choice
## 		              if (v == vNEW_VEHICLE))
## 				##
## 		newvhs.extend(di  for di,v,asap in now  if (v == vNEW_VEHICLE))
##
## 		##-----  now[]
##
## 					## ASAP/ALAP? clear preference for
## 					## immediate assignment or delay
##
## 		##=====  end of choice-enumeration magic  ====================
##
## 		backtrack.append(now)
## 		btrack_alt.append(alt)
##
## 		debugmsg('##', 1)
## 		continue
##
## 		ds = list(d  for d in dels
## 		          if ((t & d['time2vec']) and
## 		              (not is_delivery_frozen(d))))     ## 1
## 					##
## 					## deliveries (1) not yet scheduled
## 					## (2) can be delivered in this window
##
## 				## build (delivery, vehicle) pairs, listing
## 				## all vehicles which may hit this delivery
## 				##
## 				## - all specific, already traversing vehicles
## 				##   which may reach this delivery (in the
## 				##   currently checked window)
## 				##
## 				## - available but not yet started vehicles
## 				##   are assigned from a 'pool' as they
## 				##   are interchangeable. we only need to
## 				##   keep track of how many there are,
## 				##   and one is sufficient to 'assign'
## 				##   (since we do not care about which one)
## 				##
## 				## - an extra 'virtual vehicle' is added
## 				##   if delivery may be delayed. this is
## 				##   a placeholder, making it explicit that
## 				##   the delivery has been considered, but
## 				##   it does not happen now.
## 				##
## 				## - conversely, if delivery may not be
## 				##   delayed, is not reachable, and we are
## 				##   out of unassigned vehicles,
## 				##   we must backtrack.
##
## 		ds = list(sorted(ds, key=del_unit2sort))
## 		for d in ds:
## 			didx = d[ "index" ]
##
## 			debugmsg(f'## T.DELV.IDX={ didx }', 1)
## 			debugmsg(f'## T.DELV.WINDOW={ d["time"] }', 1)
##
## 			x, y = d['x'], d['y']
## 			new_load = [ d['primary'], d['secondary'] ]
##
## 			vs   = vehicle_may_reach(x, y, t, vpos, xy2d, d)
## 			vids = vehicles_which_may_deliver(new_load, vs, vpos)
##
## 			curr[ didx ] = vids
##
## 			if has_time_after(d, t) and (not asap):
## 				curr[ didx ].append([ vDELAY_DELIVERY, 0, ])
##
## 			if vids == []:
## 				if has_time_after(d, t):
## 					backtrack.append(
## 						btrack_delivery(d, delay=True) )
## 					print(f'## DELAY[{ didx }]')
## 					continue
## 				vids = [ vDELAY_DELIVERY, ]
##
## 				raise ValueError("no suitable delivery")
## 							## backtrack
##
## 			backtrack.append( btrack_delivery(d) )
##
## 				## descend into all (this.delivery, vehicle)
## 				## options
##
## 			debugmsg(f'## D.DELV.V[{didx}]=' +
## 			         f'{ ",".join(v[0] for v in vids) }', 2)
## 			debugmsg(f'## D.DELV.V.ASAP[{didx}]=' +
## 			         ",".join(f"{v[1]}" for v in vids), 2)
##
## 			continue
##
## 			if len(vids) > 1:
## 				pass
##
## 			for vid, asap in vids:
## 				backtrack.append(
## 					btrack_vehicle(vpos[vid], vid, d))
##
## 				debugmsg(f'## V.ASSIGN[{ didx }].ARRV=[{vid}]',
## 				         2, vTRC_SCHED)
##
## 				upd = vehicle2xy(vpos, vid, asap, d,
## 				                 update=True)
## 				d[ 'minutes' ] = asap
##
## 			if debug_is_active(2):
## 				list_backtrack(backtrack)
##
## 		debugmsg('##', 1)
##
## ##			if vids == []:
## ##				if has_time_after(d, t):
## ##					backtrack.append(
## ##						btrack_delivery(d, delay=True) )
## ##					print(f'## DELAY[{ didx }]')
## ##					continue
## ##				vids = [ vDELAY_DELIVERY, 0, ]
## ##
## ##				raise ValueError("no suitable delivery")
## ##
## ##			for vid, asap in vids:
## ##				backtrack.append(
## ##					btrack_vehicle(vpos[vid], vid, d))
## ##
## ##				debugmsg(f'## V.ASSIGN[{ didx }]=[{ vid }]', 2)
## ##
## ##				upd = vehicle2xy(vpos, vid, asap, d,
## ##				                 update=True)
## ##				d[ 'minutes' ] = asap
## ##
## ##			backtrack.append( btrack_delivery(d) )
## ##
## ##				## descend into all (this.delivery, vehicle)
## ##				## options
## ##
## ##			debugmsg(f'## D.DELV.V[{didx}]=' +
## ##			         f'{ ",".join(v[0] for v in vids) }', 2)
## ##			debugmsg(f'## D.DELV.V.ASAP[{didx}]=' +
## ##			         ",".join(f"{v[1]}" for v in vids), 2)
##
## 	tstart = timediff_log_now(tstart, 'PACK.ROUTE.ASSIGN0')
##
## 	##-----  tstart is after initial greedy assignment  ------------------
##
## 	vpos = vpos0
##
## 	##-----  v3:  --------------------------------------------------------
##
## 	dlist = copy.deepcopy(aux)
##
## 				## all entries, replicated from aux
## 				## sorted in increasing urgency order
## 				##
## key=del_timesort -> increasing urgency
## ##	dlist = sorted((copy.deepcopy(a) for a in aux), key=del_timesort)
##
## 	dlist = list(sorted(list(dlist), key=del_unit2sort))
##
## 	for d in dlist:
## 		idx = d[ 'index' ]
## 		if not 'start' in d:
## 			continue
##
## ##		tvec, x, y = d['time2vec'], d['x'], d['y']
## 		tvec, x, y = d['start'], d['x'], d['y']
## 		if tvec == 0:
## 			continue
##
## 		assert('start' in d)       ## must have initial-assigned by now
##
## 		print(f"##   DELIVERY={ len(place) +1 }/{ len(dlist) }")
## 		print(f"## T={ d['time'] }  [t.vec=x{ tvec :0x}]")
## 		print(f"##   START={ d['start'] }u")
## 		print("##   TW=" +timevec2utilstr(tvec, maxu, sep='',
## 		                                  unitcols=1))
##
## 		vs = vehicle_may_reach(x, y, tvec, vpos, xy2d, d)
## 		if vs == []:
## 			raise ValueError("no suitable delivery")
##
## 		primary, secondary = d['primary'], d['secondary']
## 		vid_picked, arrival = None, vTIME_UNDEF
##
## 		for v in vs:
## 			vid = v[0]
## 			v1  = vehicle2primary  (vpos[ vid ])
## 			v2  = vehicle2secondary(vpos[ vid ])
##
## 			if (primary +v1) > MAX1:
## 				print(f"##   OVERLOAD[{ vid }]: " +
## 				      f"{ primary + v1 }")
## 				continue
##
## 			if MAX2 and ((secondary +v2) > MAX2):
## 				print(f"##   OVERLOAD.SECONDARY[{ vid }]: " +
## 				      f"{ secondary + v2 }")
## 				continue
##
## 			if (vid_picked == None) or (v[2] < arrival):
## 				vid_picked, arrival = vid, v[2]
##
## 		if vid_picked == None:
## 			raise ValueError("no suitable vehicle")
##
## 		print("##  del=" +timevec2utilstr(minute2timevec(arrival),
## 		                                  maxu, sep='', unitcols=1))
## 				##
## 		print(f'## DEL { vid_picked } at { minute2wall(arrival) }')
## 		print(f'## ADD { vid_picked } {primary} sec={secondary}')
## 		vehicle2xy(vpos, vid_picked, arrival, d)
## 		print('')
## 		place.append([ vs[0], [], ])
## 				## TODO: remember alternatives
##
##
## ##					## filter vehicles which may reach
## ##					## the suitable deliverxy2dist windows
## ##		vs = vehicle_may_reach(x, y, tvec, vpos, xy2dist)
## ##		if vs == []:
## ##			raise ValueError("no suitable delivery")
## ##					## -> backtrack
## ##
## ##		primary, secondary = d['primary'], d['secondary']
## ##		vid_picked, arrival = None, vTIME_UNDEF
## ##
## ##		for v in vs:
## ##			vid = v[0]
## ##			v1  = vehicle2primary  (vpos[ vid ])
## ##			v2  = vehicle2secondary(vpos[ vid ])
## ##
## ##			if (primary +v1) > MAX1:
## ##				print(f"##   OVERLOAD[{ vid }]: " +
## ##				      f"{ primary + v1 }")
## ##				continue
## ##
## ##			if MAX2 and ((secondary +v2) > MAX2):
## ##				print(f"##   OVERLOAD.SECONDARY[{ vid }]: " +
## ##				      f"{ secondary + v2 }")
## ##				continue
## ##
## ##			if (vid_picked == None) or (v[2] < arrival):
## ##				vid_picked, arrival = vid, v[2]
## ##
## ##		if vid_picked == None:
## ##			raise ValueError("no suitable vehicle")
## ##
## ##		print("##  del=" +timevec2utilstr(minute2timevec(arrival),
## ##		                                  maxu, sep='', unitcols=1))
## ##		print(f'## DEL { vid_picked } at { arrival }')
## ##		print(f'## ADD { vid_picked } {primary} sec={secondary}')
## ##		vehicle2xy(vpos, vid_picked, arrival, d)
## ##		print('')
## ##		place.append([ vs[0], [], ])
## ##				## TODO: remember alternatives

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
##   'nr.points': ...just to simplify for human readers...
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
				dist = xy2minutes(src[0], src[1],
				                  dst[0], dst[1])
			cost[-1].append(dist)

	res = {
		'nr.points': len(pts),
		'points':    pts,
		'time':      cost,
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

		tgth = t[0]  if (t[0] != '')  else 'localhost'
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
	tstart = timediff_log_now(tstart, 'BFD')

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

