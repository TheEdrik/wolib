#!/usr/bin/python3

## retrieve vehicle (single-vehicle) and dispatcher (multi-vehicle)
## table views from pack-and-route output.
##
## CSV output; controlled by environment
##   VEHICLE=...    all stops for a single vehicle; raises exception if invalid
##   FULLPLAN=...   one column per vehicle; rows in arrival order
##   FULLFRAME=...  add full vehicle+time frame even for single-vehicle output
##   NOCOORDS=...   list only delivery times, no coordinates
##   MULTICOL=...   force all entries (delivery, X, Y) into its own column
##
## default mode:
##         all vehicles, one full column for each one, fully
##         packed (nr. rows == nr. of stops for worst-case vehicle)
##
## multi-vehicle formats add a common time column
##
## most code shared with pack.py; see log2sched()


## input format, basic:
##    SCHED VEH=VEHICLE09,T=135min,DELV=15,STOP=3
##          -- vehicle nr.9 delivers #16 at T=135 minutes.
##
##    ASSIGN.V[VH=VEHICLE00,DELV=128]=X=0.512286,Y=0.110788,T.ARRV=0min
##          -- delivery 'DELV' is at X=..., Y=...
##          -- not part of schedule output, only related-but-present byproduct
##
## intermediate format:
##     [ vehicle, delivery, time ] tuples


##--------------------------------------
import re, fileinput, os, sys


## TODO: replicated; turn to library
vHR_MIN =  8     ## min(schedule delivery), hours HH00


## both expressions must match for line to be recognized
##
## captures vehicle ID to 'vid'
reVEHICLE = re.compile('SCHED \s.* VEH= (?P<vid>[^,]+)',
                       re.VERBOSE | re.IGNORECASE)
##
## captures time (minutes) ID to 'time'
reTIME = re.compile('SCHED \s.* T= (?P<time>\d+) min',
                    re.VERBOSE | re.IGNORECASE)
##
## captures delivery ID to 'delv'
reDELV = re.compile('SCHED \s.* DELV= (?P<delv>\d+)',
                    re.VERBOSE | re.IGNORECASE)
##
## captures delivery ID to 'delv', coordinates to 'x' and 'y'
##
reXY = re.compile('ASSIGN.V .* DELV= (?P<delv>\d+) .* ' +
                  'X= (?P<x> [^,]+) .* Y=(?P<y> [^,]+)',
                  re.VERBOSE | re.IGNORECASE)
##
## TODO: depends on X=...,Y=..., ordering (which is the natural one)
## yes, we are aware that 'ASSIGN.V' matches any character, not just
## a verbatim '.'


## TODO: replicated; turn to library
##--------------------------------------
def minute2wall(m):
	"0-based minutes to 24-hour wall-clock time [string]"
	m += vHR_MIN * 60
	return f"{ m //60 :02}{ m %60 :02}"


##--------------------------------------
## returns [ vehicle, delivery, time ] tuples for each scheduled delivery,
## and { delivery: [ X, Y ] } coordinate list
##
def lines2delvs(lines):
	res, xys = [], {}

	for l in lines:
		vid  = re.search(reVEHICLE, l)
		t    = re.search(reTIME,    l)
		delv = re.search(reDELV,    l)
		##
		if vid and t and delv:
			res.append([
				     vid.group('vid'),
				int( delv.group('delv'), ),
				int( t.group('time'),    ),
			])
			continue

		xy = re.search(reXY, l)
		if xy:
			d, x, y = xy.group('delv'), xy.group('x'), xy.group('y')
			##
			xys[ int(d) ] = [ x, y, ]
			## continue

	return res, xys


##--------------------------------------
if __name__ == '__main__':
	targetveh = None

	lines = list(l.rstrip() for l in fileinput.input())
	table, xys = lines2delvs(lines)

	ts, ds, vs = set(), set(), set()
	##
	for vid, t, delv in table:
		ds.add(delv)
		vs.add(vid)
		ts.add(t)

			## build full matrix
			## we do not care about single-vehicle inefficiency

	vehs  = list(sorted(vs))                           ## all vehicles
	allts = list(sorted(ts))                           ## all time(minutes)

	if 'VEHICLE' in os.environ:
		targetveh = os.environ[ 'VEHICLE' ]
## TODO: multi-vehicle -> split -> use multi-valued... would come here
		##
		if not targetveh in vehs:
			raise ValueError(f"unknown vehicle ({ targetveh })")

		vehs = [ targetveh ]

			## interesting times to any of the relevant vehicles
			## note: possibly already available in single-matrix
			## view; we reconstruct it (redundant)
	tmin, vmin = {}, {}

			## build tmin[ ...m... ] = [ ...delivery: vehicle ]
			## and vehicle->delivery indexes (table row)

	for v in vehs:
		vdts = [vdt  for vdt in table  if (v == vdt[0])]
		for _, d, t in vdts:
			if not t in tmin:
				vmin[ t ] = {}
			if not t in tmin:
				tmin[ t ] = {}
			vmin[ t ][ v ] = d
			tmin[ t ][ d ] = v
						## TODO: report inconsistency

			## tmin.keys() lists all relevant minutes
			## (when delivery happens)

	print('xxx.t', tmin)
	print('xxx.tk', sorted(tmin.keys()))
	print('xy', xys)
	print('xxx', ts, ds, vs)

	res = []
	timecol = False 

						## header: list of vehicle IDs
	if (len(vehs) > 1) or ('FULLFRAME' in os.environ):
		res.append([ 'T' ])
		res[-1].extend(vehs)
		timecol = True

	##-----  partial matrix
	## when collapsing per-vehicle (time) columns, remap times ->
	## display remaps missing entries
## TODO

	##-----  full matrix: all time rows  ---------------------------------
	for t in sorted(tmin.keys()):
		r = []

		if timecol:
			r.append( minute2wall(t) )

		for v in vehs:
			if (not t in vmin) or (not v in vmin[t]):
				r.append('')
				continue

			delv = vmin[t][v]

			if not delv in xys:
				raise ValueError("no delivery coordinates " +
				                 f"(D={ delv })")

			r.append(f'D={ delv }')

			if not 'NOCOORDS' in os.environ:
				x, y = xys[ delv ]
				r[-1] += f':X={x}:Y={y}'

		res.append(r)

## TODO: use CSV-constructor from library
	print("## CSV start:")
	for r in res:
		print(','.join(r))

