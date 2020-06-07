#!/usr/bin/python3

import fileinput, sys, math, csv, operator
import xy2path                     ## X+Y -> 1D fractal distance mapping; table

## pass X,Y in 2-column CSV, [0.0 .. 1.0]
##
## table in xy2path.tTABLE[] MUST have been generated by 2D/fractal generator
## it is indexed 0..2^N in both dimensions


##--------------------------------------
## returns array of <x, y> pairs
## no normalization etc., beyond range checking
##
def table_read(fname, field=1):
	csvf = open(fname, newline='')
	rd   = list(csv.reader(csvf, delimiter=',', quotechar='\\'))
	res  = []

	for fi, fields in enumerate(rd):
		if len(fields) < 2:
			raise ValueError("missing primary/secondary+value " +
			                 f"columns (line {fi +1})")
		try:
			x, y = float(fields[0]), float(fields[1])
		except ValueError:
			raise ValueError("malformed input: "+
			                 f"[{fields[0]},{fields[1]}]")

		if not (0.0 <= x <= 1.0):
			raise ValueError(f"X out of range {x} (line {fi +1})")
		if not (0.0 <= y <= 1.0):
			raise ValueError(f"Y out of range {y} (line {fi +1})")

		res.append([x, y])

	return res


##--------------------------------------
def terminate(msg):
	sys.stderr.write(msg +'\n')
	sys.exit(-1)


##--------------------------------------
def usage():
	terminate("""
	Route 2D paths through space-filling functions
	Usage: [MAXN==...]  ... <name of input CSV containing X+Y coordinates>
	...usage blurb comes here...
	""")


##--------------------------------------
## works both for [x, y] (0.0 .. 1.0) and [x, y, x', y'] (2x2, incl. normalized)
##
def dumppath(p):
	print('\n'.join(f'{v[0]} {v[1]}' for v in p))


##--------------------------------------
## returns 2x floats normalized to [0 .. 2^N], plus curve-distance(x,y)
##
## TODO: check square table during reading
##
def xy2tablexy(x, y, table):
	"normalize [0.0 .. 1.0] coordinates to [0 .. 2^N] dimensions"

	xi, yi = x * len(table), y * len(table)

	return xi, yi, table[ round(xi) ][ round(yi) ]


##--------------------------------------
def xy2dist(xy1, xy2):
	return math.sqrt((xy1[0] - xy2[0]) **2 + (xy1[1] - xy2[1]) **2)


##--------------------------------------
## any array-of-tuples input with (x, y...) start is acceptable
## route is not closed: excludes loop-completing edge
##
def route2dists(xys):
	return (xy2dist(xys[i], xys[i+1])  for i in range(len(xys)-1))


##--------------------------------------
## any array-of-tuples input with (x, y...) start is acceptable
## route is not closed: excludes loop-completing edge
##
def route2total(xys):
	return sum(route2dists(xys))


##--------------------------------------
## tolerates, silently ignoring negative indexes
## repeated entries are counted only once
##
def idx2bitmask(arr):
	return sum((1 << v)  for v in set(arr)  if (v >= 0))


##----------------------------------------------------------------------------
## incremental swap costs, exchanging [i] and [j]:
##   ---[i-1]-------[i]-------[i+1]---
##           \     /   \     /
##             \ /       \ /         
##              =         =         
##             / \       / \ 
##           /     \   /     \
##   ---[j-1]-------[j]-------[j+1]---
##                      d(X, Y) == distance(X .. Y)
##   swap [i] and [j]:
##      - removes  d(i-1, i) +d(i, i+1)
##      - removes  d(j-1, j) +d(j, j+1)
##      - adds     d(i-1, j) +d(j, i+1)
##      - adds     d(j-1, i) +d(i, j+1)


##--------------------------------------
## find swaps which may be performed simultaneously and reduce total
## route length the most: swap position of points [i] and [j]
##
## returns list of index pairs to swap
##         None  no improvement found during any of the swaps
##
## 'swaps' stores [index1, index2, bitmask(all affected indexes)]
## we can hypothetically swap all length-reducaing candidates which do not
## overlap (therefore the bitmasks)
##
def swap1(xys):
	swaps = []

	for i in range(1, len(xys)-3):
			## [i-1] -> [i] -> [i+1] -> [i+2]  swap, simplified:

		rem =  xy2dist(xys[ i-1 ], xys[ i   ])
		rem += xy2dist(xys[ i+1 ], xys[ i+2 ])
		add =  xy2dist(xys[ i-1 ], xys[ i+1 ])
		add += xy2dist(xys[ i   ], xys[ i+2 ])

		if (add -rem < 0):
			print(f'# {i}x({i}+1) +{add:.04f} -{rem:.04f} ' +
			      f'bal={add-rem:.06f}')
			sys.stdout.flush()
			swaps.append([i, i+1,
			              idx2bitmask([i-1, i,   i+1,
			                             i, i+1, i+2]),
			              add])

		for j in range(i+2, len(xys)-2):
			rem += xy2dist(xys[ i-1 ], xys[ i   ])
			rem =  xy2dist(xys[ i   ], xys[ i+1 ])
			rem += xy2dist(xys[ j-1 ], xys[ j   ])
			rem += xy2dist(xys[ j   ], xys[ j+1 ])

			add =  xy2dist(xys[ i-1 ], xys[ j   ])
			add += xy2dist(xys[ j   ], xys[ i+1 ])
			add += xy2dist(xys[ j-1 ], xys[ i   ])
			add += xy2dist(xys[ i   ], xys[ j+1 ])

			if (add -rem >= 0.0):
				continue

			print(f'# {i}x{j} +{add:.04f} -{rem:.04f} ' +
			      f'bal={add-rem:.06f}')
			sys.stdout.flush()

			swaps.append([i, j,
			              idx2bitmask([i-1, i, i+1,
			                           j-1, j, j+1]),
			              add -rem, ])

		## swaps[-1] is the current-best pair
		## check if any preceding swap pairs might be simultaneously
		## applied (their bitmasks do not overlap)
		##
		## need not be optimal here: leaving any un-swapped here will
		## still get considered in the next iteration.  therefore,
		## simply scanning backwards and collating all bitmasks
		## ('swapbm') without further filtering, is sufficient

	if swaps == []:
		return None

	swaps  = list(sorted(swaps, key=operator.itemgetter(3)))
	pairs, swapbm = [], 0

		## pick up pairs in decreasing-improvement order
		## ...if the new swap does not conflict with any
		## already accepted one
		##
	for x, y, bm, diff in reversed(swaps):
		if (swapbm & bm):
			continue
		swapbm |= bm
		pairs.append([x, y])
		print(f"## SWAP+ {x} {y}")

	return pairs


##--------------------------------------
## find reorders which improve total path lengths: moving [i] to
## to after [j] and before [j+1]:
##     [i-1] -> [i] -> [i+1] ... [j] ->        [j+1]   becomes
##     [i-1]        -> [i+1] ... [j] -> [i] -> [i+1]
##
## j >= i+2; j == i+1 has been covered by pairwise swaps
##
## returns list of index pairs to reorder, [i, j] tuples
##         None  no improvement found during any of the swaps
##
## 'reord' stores [index1, index2, bitmask(all affected indexes)]
## we can hypothetically swap all length-reducaing candidates which do not
## overlap (therefore the bitmasks)
##
def move1(xys):
	reord = []

	for i in range(1, len(xys)-3):
		for j in range(1, len(xys)-3):
			if (i == j) or (i+1 == j) or (i == j+1):
				continue

			rem =  xy2dist(xys[ i-1 ], xys[ i   ])
			rem += xy2dist(xys[ i   ], xys[ i+1 ])
			rem += xy2dist(xys[ j   ], xys[ j+1 ])
				##
			add =  xy2dist(xys[ i-1 ], xys[ i+1 ])
			add += xy2dist(xys[ j   ], xys[ i   ])
			add += xy2dist(xys[ i   ], xys[ j+1 ])

			if (add -rem) >= 0.0:
				continue

			print(f'# {i}->{j}+1 +{add:.04f} -{rem:.04f} ' +
			      f'bal={add-rem:.06f}')
			sys.stdout.flush()

			reord.append([i, j,
			             idx2bitmask([i-1, i, i+1, j, j+1]),
			             add -rem, ])
	if reord == []:
		return None

	reord  = list(sorted(reord, key=operator.itemgetter(3)))
	moves, movebm = [], 0

	for r in reord:
		i, j, bm = r[0], r[1], r[2]
		if (movebm & bm):
			continue
		movebm |= bm
		moves.append([i, j])
		print(f"## MOVE {i}->{j}+1")
	return moves


##----------------------------------------------------------------------------
if __name__ == '__main__':
	sys.argv.pop(0)
	if [] == sys.argv:
		usage()

	xys = table_read(sys.argv[0])
	xys = list([x, y, xy2tablexy(x, y, xy2path.tTABLE)[0],
	                  xy2tablexy(x, y, xy2path.tTABLE)[1],
	                  xy2tablexy(x, y, xy2path.tTABLE)[2],]
	           for x,y in xys)

	print("# INITIAL=")
	for p in xys:
		print(f'# {p[2]},{p[3]}')
	print()

			## initial plan: assign on curve
	xys = list(sorted(xys, key=operator.itemgetter(4)))

	round, dist0 = 0, route2total(xys)
	dist = dist0

	print(f"# SORTED.ROUND={round}")
	print(f"# DIST0={ dist }")
	print(f"# DIST={ 100.0* dist / dist0 :.02f}%")
	##
	for p in xys:
		print(f'{p[2]},{p[3]}')
	print()

	while True:
		imprd, round = 0, round +1

		swaps = swap1(xys)

		if swaps != None:
			route0 = route2total(xys)
			best   = route0

			print(f"##SWAP1.ROUND={round}")
			for i, j in swaps:
				print(f"##SWAP {i},{j}")
				xys[i], xys[j] = xys[j], xys[i]
				imprd += 1

				curr = route2total(xys)
				if (curr > best):
					raise ValueError("non-decreasing swap")
				best = curr
			for p in xys:
				print(f'{p[2]},{p[3]}')
			print()
			sys.stdout.flush()

			curr = route2total(xys)
			print(f'## TOTAL.S={ curr }')
			if (curr > route0):
				raise ValueError("non-decreasing swap")


			## unlike swaps, which preserve indexes, movement
			## needs to adapt as it shifts indexes: f.ex.,
			## moving (2 -> 5+1) removes element [2], so
			## a subsequent (3 -> 10+1) move would need to
			## remove [2] instead of [3] after the preceding
			## move
			##
			## 1) remove elements into temp array; replace
			##    them with placeholders.  mark if placeholders
			##    are touched again as they SHOULD NOT be
			##    (moves are non-overlapping)
			## 2) add elements in decreasing-index order
			## 3) discard placeholders

		reord = move1(xys)
		if reord != None:
			route0 = route2total(xys)
			moved  = []    ## stores [target index, [...element...],
			               ##          orig.index]
			               ## orig. index is redundant, just for log

					## removal may proceed in arbitrary
					## order: entries only marked deleted
					## (set to None)
			for i, j in reord:
				if (j == i+1):
					raise ValueError("in-place reorder?")
				if (xys[i] == None):
					raise ValueError("overlapping moves? "+
					                 f"(element {i})")
				moved.append([j, xys[i], i])
				xys[i] = None                ## mark as removed

					## add back moved entries, decreasing
					## index order

			for m in sorted(moved, key=operator.itemgetter(0),
			                reverse=True):
				xys.insert(m[0]+1, m[1])
				imprd += 1

					## purge marked-as-deleted entries
			xys = list(x  for x in xys  if (x != None))

			curr = route2total(xys)
			print(f'## TOTAL.S={ curr }')
			if (curr > route0):
				raise ValueError("non-decreasing swap")

		if imprd == 0:
			break

