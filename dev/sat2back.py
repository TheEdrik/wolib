#!/usr/bin/python3

## turn back standalone SAT-solver output to packer-readable form
##
## sanity-checks values if 'VERIFY' is present in environment
## reverses to human-readable schedule form for variables
## in canonical form
## see satsolv_var_name() in pack.py for variable-naming rules
##
## set 'SCHEDULE' to recreate rough overview of typical SAT assignments
## if they follow our scheduler policies:
##    dXXtYY
##    dXXtYYvZ  v0..vN   N+1-bit vehicle ID (VID): delivery +time unit +vid.bit
##    dXXvZ     v0..vN   
##
## set 'ROLL' to tolerate certain errors in response
##    see roll() for list
##
## set 'FULL_VARS' to list even unnecessary variables
##   example: dXXtYY (delivery XX time unit YY) is False if none of the
##   dXXtYYvZZ vehicle-ID bits are False. the entire group may be skipped
##   in such cases.
##
## set 'LIST_NUM' to include numeric ID for symbolic names
##
## set 'ADDED_VARS' to list indirect variables' values too. they
## are excluded from response list by default.
##
## adds constraints with 'CONSTRAIN' set in environment:
##    X           (variable nr/name)  set X as true
##    '!...X...'  set X as false
##    '-...X...'  set X as false
##    may supply multiple terms; '-' or '0' separate them as clauses
##
## requires pack-and-route result (for variable/name mappings) and
## SAT solver DIMACS-formatted result
##
## see satsolv_report() in pack-and-route for formatting. we extract
## the VARIABLES section:
##     -----------------------
##     c VARIABLES:
##     c   d0t2[1] d0t2v0[2] d0t2v1[3] d0t2v2[4] d0t2v3[5] d0t2v4[6]
##     c   d0t3[7] d0t3v0[8] d0t3v1[9] d0t3v2[10] d0t3v3[11] d0t3v4[12]
##     ...
##     c /VARIABLES
##     -----------------------
##         (1) tolerate+ignore leading "c ...whitespace..." (DIMACS comment)
##         (2) IDs are all-letter+digit
##         (3) numeric indexes are >0
##
## response (only minimal parsing):
##     -----------------------
##     ...
##     s SATISFIABLE
##     v -1 -2 -3 -4 -5 -6 7 8 -9 ...
##     ...
##     v -13098 -13099 0
##     ...
##     -----------------------
##         response processing stops at the first "0"
##
## DIMACS format (simplified version):
##     Jaervisalo, Le Berre, Roussel: Rules of the 2011 SAT competition
##     www.satcompetition.org/2011/rules.pdf, section 4.1
## accessed 2023-02-27
## SHA1()=xb08ad0aca66821ee85fb8e05650340f6180db386
## SHA256()=xcab5a36e6dda3efef32be201838012d03a901c04ef3556762442b5010aaeb479
##
## we expect to read entire files, and not use a streaming API.
## please do not comment on inefficiency, or the expectation that
## we only deal with reasonably small inputs.
##
## Author: Visegrady, Tamas  <tamas.visegrady@gmail.com>

import re, sys, os, fileinput
import sat_tools


##-----------------------------------------
reVARDEF = re.compile('(?P<id> [a-zA-Z0-9] [a-zA-Z0-9_]*) \[ (?P<nr> \d+) \]',
                      re.VERBOSE)
##
## match "d0t4v0[14]" -> id = d0t4v0, nr = 14

## TODO: do we have a global constant?
vUNIT_MINS = 15

reOK   = re.compile('^ s \s+ SATISFIABLE$ ',         re.VERBOSE)
reFAIL = re.compile('^ s \s+ UNSATISFIABLE$ ',       re.VERBOSE)

reRESPONSES = re.compile('^ v \s+', re.VERBOSE)


##-----------------------------------------------------------
## capture patterns
##
## all feature 'delivery'
## the patterns are redundant; please do not comment on it
##
## delivery, time unit (del, t)
reDT = re.compile('^ d (?P<del>\d+) t (?P<t>\d+) $', re.VERBOSE)
##
## delivery, vehicle-ID bit (del, bit)
reDV = re.compile('^ d (?P<del>\d+) v (?P<bit>\d+) $', re.VERBOSE)
##
## delivery, time, vehicle-ID bit (del, t, bit)
reDTV = re.compile('^ d (?P<del>\d+) t (?P<t>\d+) v (?P<bit>\d+) $',
                   re.VERBOSE)


##-----------------------------------------
## tolerate errors? set to >0 if so:
##   (1) mild ones only
##   (2) any error
##
vROLL = False


##----------------------------------------------------------------------------
## read DIMACS spec (input); parse complete list of clauses
##
## optionally, parses output into array-of-ints (variables), if present
## (if 'result' is non-None; list/iterator of result lines)
##
## cross-checks that main parameters of input+output seem to match
##
def sat2values(dimacs, result=None):
	return res


##----------------------------------------------------------------------------
## returns None for other variables
def var2dt(varname):
	dt = re.match(reDT, varname)
	if dt:
		return [ dt.group('del'), dt.group('t') ]

	return None


##----------------------------------------------------------------------------
## dXXtYYvZZ to dXXtYY etc.; reconstruct logical grouping
## returns None for other, unrecognized var.names
##
## matching is minimal
##
def var2parent(varname):
	if varname.startswith('d') and ('v' in varname):
		return varname[ : varname.index('v') ]

	return None


##----------------------------------------------------------------------------
## retrieve VARIABLES section, populate reverse maps
## return None if file is not recognized
##
## registers keys (ints) >0
## tolerate repeated identical assignments; ensures mapped-int unicity
##
def vars2list(lines):
	matches = list(li  for li, l in enumerate(lines)
	                   if re.search('VARIABLES', l))

	if len(matches) != 2:
		return None

	all = list(re.sub('^c\s+', '', l)  for l in lines)

	if ('/VARIABLES' in all[ matches[0] ]):
		sys.stderr.write("no VARIABLES start tag; " +
				"is this really our SAT-solver input?\n")
		return None

	if not ('/VARIABLES' in all[ matches[1] ]):
		sys.stderr.write("no /VARIABLES terminating tag; " +
					"accepting possibly partial input\n")

	all  = all[ matches[0]+1 : matches[1] ]     ## VARIABLES ... /VARIABLES
	res  = {}
	back = {}

	for l in (r.split()  for r in all):
		for elem in l:
			m = re.match(reVARDEF, elem)
			if m == None:
				sys.stderr.write("can not parse SAT-variable " +
					f"assignment ({elem})\n")
				return None

			id, nr = m.group('id'), m.group('nr')

			if nr == 0:
				sys.stderr.write("invalid SAT-variable ID 0\n")
				return None

					## tolerate identical redefinitions
					## report other
			if nr in res:
				if res[ nr ] == id:
					continue
				sys.stderr.write("invalid SAT-variable " +
					f"redefinition ({nr}: {id} vs. " +
					f"{ res[nr] })\n")
				return None
			else:
				res [ nr ] = id
				back[ id ] = nr

	return res, back


##-----------------------------------------
## is this ID that of an added/indirect variable?
##
def is_indirect_var(v):
	return v.startswith('N')                            ## was: 'N' or 'NV'


##-----------------------------------------
## return 2x list, of signs ('-' or empty) and of sign-less IDs
##
## input is list of text IDs
##
def satsolv_str2ids(ids):
	sgns = list(('-'  if (i[0] == '-')  else '')  for i in ids)
	curr = list(re.sub('^-', '', i)  for i in ids)

	return sgns, curr


##-----------------------------------------
## map back integers from 'vars' to string inputs
## 'lut' is integer-to-table, containing >0
##
## response maps True/False to all inputs, or None if not defined
##
def satsolv_ints2strings(vars, lut):
	res = dict.fromkeys(lut.values())        ## default value None

	for r in vars:
					## split each to sign ('-' or empty)
					## and base string
		signs, curr = satsolv_str2ids(r.split())

		for i, nr in enumerate(curr):
			if nr == '0':
				break

			if not nr in lut:
				sys.stderr.write(f"ERROR: unknown variable "+
						f"ID: [{ id }]\n")
				return None

			id = lut[ nr ]
			v  = (signs[i] != '-')

					## tolerate identical redefinition
			if (res[ id ] != None) and (res[ id ] == v):
				continue

			res[ id ] = v

	return res


##-----------------------------------------------------------
## locate variables in known-canonical form of solver output
## turn them back to schedule-relevant inputs
##
## returns dicts (see list in end); no consistency checking yet
##
## input is { 'name': Boolean } dictionary
##
def solv2vars(res):
	delvs, tunits, vbits = {}, {}, {}           ## list of all D,T,V's seen
	dtvs = {}           ## [ delivery ][ time  ][ v.bit ]
	dts  = {}           ## [ delivery ][ time  ]
	dvs  = {}           ## [ delivery ][ v.bit ]
						## captured individually
						## cross-checked in the end

	for r in res:
		d, t, v = None, None, None
		value = res[r]

		while True:                         ## break from first capture
			dtv = re.match(reDTV, r)
			if dtv:
				d, t = dtv.group('del'), dtv.group('t')
				v    = dtv.group('bit')
				break

			dt = re.match(reDT, r)
			if dt:
				d, t = dt.group('del'), dt.group('t')
				break

			dv = re.match(reDV, r)
			if dv:
				d, v = dv.group('del'), dv.group('bit')
				break

			break

		if (d == None) and (t == None) and (v == None):
			continue

		d = int(d)                        ## delivery is always present
		if t != None:
			t = int(t)
		if v != None:
			v = int(v)

		delvs[ d ] = 1

		if (not d in dtvs):
			dtvs[ d ] = {}
		if (not d in dts):
			dts[ d ] = {}
		if (not d in dvs):
			dvs[ d ] = {}

		if t != None:
			tunits[ t ] = 1
			if (not t in dts[d]):
				dts[d][t] = {}

			if v != None:
				if (not t in dtvs[d]):
					dtvs[d][t] = {}
				if (not v in dtvs[d][t]):
					dtvs[d][t][v] = value

		if v != None:
			vbits[ v ] = 1
			if (not v in dvs[d]):
				dvs[d][v] = value

		continue

	return {
		'delv-time':     dts,
		'delv-vid':      dvs,
		'delv-time-vid': dtvs,
	}


##--------------------------------------
## collapse full-range lists to START..END
## expect to run on reasonably short lists of integers
## returns pretty-print string
##
def list2str(lst):
	arr = list(sorted(lst))

	minv, maxv = arr[0], arr[-1]

	if (maxv - minv) == len(arr) -1:
		return f"{ minv }..{ maxv }"
	else:
		return ",".join(str(v)  for v in arr)


##--------------------------------------
## encode big-endian array of Booleans to unsigned int
##
def booleans2int(arr):
	return sum((1 << (len(arr) - ai -1))  if arr[ai]  else 0
	           for ai, a in enumerate(arr))
##
## TODO: is there a centralized version in vt.py?


##----------------------------------------------------------------------------
def roll(level=1):
	if vROLL == False:
		return False

	return (level <= vROLL)


##----------------------------------------------------------------------------
## returns [ hour(start), minutes(star), hours(end), minutes(end) ]
## see timevec2wall() in pack.py
##
## 'unit0' is BCD-encoded
##
def unit2clock(u, unit0=800, unit=15):
	hr, mn = (unit0 // 100), (unit0 % 100)

	if (u < 0):                                     ## ...or max(range)...
		raise ValueError(f"invalid time unit ({u})")

## TODO: proper time propagation; we only base against default unit0

	mn += u * unit
	hr += (mn // 60)
	mn %=  60

	return [ hr, mn, hr, mn +unit -1 ]


##----------------------------------------------------------------------------
## unit to HHMM-HHMM range
##
def unit2wallclk(u):
	clk = unit2clock(u)

	return f'{ clk[0] :02}{ clk[1] :02}-{ clk[2] :02}{ clk[3] :02}'


##----------------------------------------------------------------------------
## is the recovered set of dicts-of-variables consistent?
## excepts if arrays are trivially malformed
##
def vars2check(dicts):
	delvs = sorted(dicts[ 'delv-time' ].keys())

				## explode if not reading all cross-lists
				## each dict indexes (full list of) deliveries

	if (delvs != sorted(dicts[ 'delv-vid' ].keys())) and not roll():
		raise ValueError("delv.list(vehicle IDs) != delv.list(time)")

	if (delvs != sorted(dicts[ 'delv-time-vid' ].keys())) and not roll():
		raise ValueError("delv.list(vehicle IDs) != " +
					"delv.list(delivery+time)")

	tunits, vbits = {}, {}
	for d in delvs:
		for t in dicts[ 'delv-time' ][ d ]:
			tunits[ t ] = 1
	tunits = list(sorted(tunits.keys()))

					## all vehicle-ID bits must be
					## present in each delv x time pair
					## pick arbitrary row to check size
	tsample = list( dicts[ 'delv-time-vid' ][ delvs[0] ].keys() )[0]
					##
	vbitcount = len(dicts[ 'delv-time-vid' ][ delvs[0] ][ tsample ])

					## every delv x time pair MUST specify
					## this number of vehicle-ID bits
	dtv = dicts[ 'delv-time-vid' ]

	vplan = {}			## collect vehicle plans
	                                ## vehicle[ v.id ][ t0: delvivery ... ]

	for d in delvs:
		for t in dtv[ d ]:
			vi = booleans2int(dtv[ d ][ t ])        ## int(vehicle)
			if vi and (not vi in vplan):
				vplan[ vi ] = {}
				print(f"## VEH.ID[DELV={ d },T={ t }]={ vi }")

			if vbitcount != len(dtv[ d ][ t ]):
				actual = len(dtv[ d ][ t ])
				raise ValueError("inconsistent nr. of "
				      f"vehicle-ID bits: DELV={d},TIME={t} " +
				      f" ({actual} vs. expected {vbitcount})")
			if vi:
				if t in vplan[ vi ]:
## TODO: ROLL; clean up error return
					if (d != vplan[ vi ][ t ]) and False:
						raise ValueError(f"conflict: " +
								"D/T/V")
				vplan[ vi ][ t ] = d

		for vb in dtv[ d ][ t ].keys():
			vbits[ vb ] = 1

	vbits = list(sorted(vbits.keys()))

	print(f"DELV.LIST={ list2str(delvs) }")
	print(f"TIME.UNITS={ list2str(tunits) }")
	print(f"VEHICLE.ID.BITS={ list2str(vbits) }")

## TODO: factor out to a plan-to-schedule fn
##
	print(f"## VEHICLE.PLANS[{ len(vplan) }]:")
	for d in sorted(vplan.keys()):
		ts = sorted( vplan[d].keys() )
		if ts == 0:
			continue               ## only with optional deliveries

		print(f"VEH[{ d }].STOPS[{ len(ts) }]:", end='')

						## T=...[+..],D=...
						##
		fmt = [ f'T[{ ti+1 }]={ unit2wallclk(t) }' +
			f'{ f"[+{ vUNIT_MINS * (t - ts[ti-1]) }m]"  if ti  else "" },' +
			f'D={ vplan[d][t] }'
			for ti, t in enumerate(ts) ]

		print(";".join(fmt))

	print("## /VEHICLE.PLANS")

			## vehicle ID rows MUST be all-False, except for
			## one time unit, for each delivery

			## (1) exactly one time active for each delivery
			##     (without optional schedules)
			## (2) delivery ID dXX tYY is consistent with
			##     times
			## (3) collect max(vehicle ID) in the process
	vid = -1
	vseen = {}

	for d in delvs:
		dts = list(sorted(t  for t in
		           dicts[ 'delv-time-vid' ][d].keys()))

		print(f'## DELV.UNITS D={d}', dts)

			## time units with d/t/v not all-False
			## note: max(False, True) == True
			##
		t = [ u  for u in dts
		      if (max(dicts[ 'delv-time-vid' ][d][u].values()) == True) ]

		if t == []:
			raise ValueError(f"no delivery time (D={ d })")
## TODO: handle optional deliveries: those with legitimately no
## delivery times

		print(f'## TIME.SCHEDULED(D={d})={t}u({ unit2wallclk(t[0]) })')

		if (len(t) > 1) and not roll():
			raise ValueError(f"redundant delivery times? (D={d}," +
					f"T={ t })")

		thisv = dicts[ 'delv-time-vid' ][d][ t[0] ]
		v     = booleans2int(thisv)
		if not v in vseen:
			vseen[ v ] = []
		vseen[ v ].append(d)

		vid = max(vid, v)
		print(f'## VEH.ID({ d })=[{ v }]{ thisv }')
		print(f'## MAX(VEHICLE.ID)={ vid }')

	print('## VEHICLES', list(sorted(vseen.keys())))
	print('## VEHICLES', vseen)


##----------------------------------------------------------------------------
def verify(res):
	v = solv2vars(res)
	vars2check(v)


##-----------------------------------------------------------
if __name__ == '__main__':
	sched = ('SCHEDULE' in os.environ)

	if ('ROLL' in os.environ):
		vROLL = int(os.environ[ 'ROLL' ])

	if len(sys.argv) < 2:
		sys.stderr.write(
			"Recover pack+route variables from SAT solver log.\n"
			"Usage: <...solver input...> " +
			"[...SAT-solver response...]\n")
		sys.exit(2)

	try:
		vars = open(sys.argv[1], 'r').read().split("\n")
		sys.argv.pop(1)
	except:
                sys.stderr.write(f"ERROR: read [{ sys.argv[1] }] failed\n")
                sys.exit(1)

	clauses = sat_tools.dimacs2clauses(sat_tools.dimacs2clauses_itr(vars))
	if 'NORMALIZE' in os.environ:
		comm       = sat_tools.dimacs2comments(vars)
		maxv, seen = sat_tools.clauses2varlimits(clauses)

## note: assume ASCII host
		print(f'p cnf { maxv } { len(clauses) }')
		if comm:
			print('c')
			print('\n'.join(sat_tools.comments2print(comm)))
			print('c')
		print('\n'.join(sat_tools.clauses2print(clauses)))
		sys.exit()

	v2ints, ints2v = vars2list(vars)
	if v2ints == None:
                sys.stderr.write(f"ERROR: invalid ID-to-number mapping\n")
                sys.exit(1)

	lines = list(fileinput.input())

	ok    = list(li  for li, l  in enumerate(lines)  if re.match(reOK,   l))
	fail  = list(li  for li, l  in enumerate(lines)  if re.match(reFAIL, l))

## exit(2) for unexpected response structures

	if min(len(ok), len(fail)) != 0:
		sys.stderr.write(f"ERROR: ambiguous SAT response\n")
		sys.exit(2)

	if max(len(ok), len(fail)) != 1:
		sys.stderr.write(f"ERROR: multiple SAT responses?\n")
		sys.exit(2)

	if len(ok) == len(fail):
		sys.stderr.write(f"ERROR: both pass/fail SAT responses\n")
		sys.exit(2)

	if fail:
		sys.stderr.write(f"NO SOLUTION FOUND\n")
		sys.exit(1)

	if not ok:
                sys.stderr.write(f"ERROR: does not look like a solved "
				"SAT problem response\n")
                sys.exit(1)

	lines = list(re.sub(reRESPONSES, '', l)  for l in lines[ ok[0]+1 : ]
	             if re.search(reRESPONSES, l))

	res = satsolv_ints2strings(lines, v2ints)

	for r in sorted(res.keys()):
		if is_indirect_var(r) and not ('ADDED_VARS' in os.environ):
			continue

		ri = f'[{ ints2v[r] }]'  if 'LIST_NUM' in os.environ  else ''

		if not 'FULL_VARS' in os.environ:
			if (var2dt(r) and not res[r]):
				continue
			vp = var2parent(r)
			if vp and (vp in res) and not res[vp]:
				continue

		print(f'  { r }{ ri }: { res[r] }')

	if 'VERIFY' in os.environ:
		verify(res)

