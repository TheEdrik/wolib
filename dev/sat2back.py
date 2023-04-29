#!/usr/bin/python3

## turn back standalone SAT-solver output to packer-readable form
##
## sanity-checks values if 'VERIFY' is presnt in environment
## reverses to human-readable schedule form for variables
## in canonical form
## see satsolv_var_name() in pack.py for variable-naming rules
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


##-----------------------------------------
reVARDEF = re.compile('(?P<id> [a-zA-Z0-9] [a-zA-Z0-9_]*) \[ (?P<nr> \d+) \]',
                      re.VERBOSE)
##
## match "d0t4v0[14]" -> id = d0t4v0, nr = 14


reOK   = re.compile('^ s \s+ SATISFIABLE$ ',   re.VERBOSE)
reFAIL = re.compile('^ s \s+ UNSATISFIABLE$ ', re.VERBOSE)

reRESPONSES = re.compile('^ v \s+', re.VERBOSE)


##-----------------------------------------
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

	all = all[ matches[0]+1 : matches[1] ]
	res = {}

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
				res[ nr ] = id

	return res


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


##-----------------------------------------------------------
## locate variables in known-canonical form; turn them back to
## schedule-relevant inputs
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


##----------------------------------------------------------------------------
## is the recovered set of dicts-of-variables consistent?
## excepts if arrays are trivially malformed
##
def vars2check(dicts):
	delvs = sorted(dicts[ 'delv-time' ].keys())

				## explode if not reading all cross-lists
				## each dict indexes (full list of) deliveries

	if delvs != sorted(dicts[ 'delv-vid' ].keys()):
		raise ValueError("delv.list(vehicle IDs) != delv.list(time)")

	if delvs != sorted(dicts[ 'delv-time-vid' ].keys()):
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

	for d in delvs:
		for t in dtv[ d ]:
			if vbitcount != len(dtv[ d ][ t ]):
				actual = len(dtv[ d ][ t ])
				raise ValueError("inconsistent nr. of "
				      f"vehicle-ID bits: DELV={d},TIME={t} " +
				      f" ({actual} vs. expected {vbitcount})")

		for vb in dtv[ d ][ t ].keys():
			vbits[ vb ] = 1

	vbits = list(sorted(vbits.keys()))

	print(f"DELV.LIST={ list2str(delvs) }")
	print(f"TIME.UNITS={ list2str(tunits) }")
	print(f"VEHICLE.ID.BITS={ list2str(vbits) }")

			## vehicle ID rows MUST be all-False, except for
			## one time unit, for each delivery

			## (1) exactly one time active for each delivery
			## (2) all non-delivery windows
	for d in delvs:
		dts = list(sorted(t  for t in
					dicts[ 'delv-time-vid' ][d].keys()))

		print('xxx.D', d, dts)


##----------------------------------------------------------------------------
def verify(res):
	v = solv2vars(res)
	vars2check(v)


##-----------------------------------------------------------
if __name__ == '__main__':
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

	v2ints = vars2list(vars)
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
		print(f'  { r }: { res[r] }')

	if 'VERIFY' in os.environ:
		verify(res)

