#!/usr/bin/python3

# simulate savings of elevator algorithm in warehouse traversal
# collecting batch of orders simultaneously

## cost function, see sketch below:
vROW   = 1                 ## cost of moving 'one SKU' distance within an aisle
vAISLE = 3                 ## per aisle; aisle0-to-2 is 2x
vSTART = 'H'               ## batch-start position


##=====  nothing user-serviceable below  =====================================

## warehouse layout: parallel shelves, with most frequently ordered SKUs
## centered, both in aisle1 and within aisles
##
##                 corridor0      **dropoff**
##  A         D | G         J | M         P
##  B  aisle  E | H  aisle  K | N  aisle  Q
##  C         F | I         L | O         R
##                 corridor1
##
## batch collection starts next to most frequently ordered SKUs [H,K],
## terminates at **dropoff**
##
## traversal costs are hierarchical, aisle-to-aisle plus SKU to SKU
##
## 'group' (=aisle) is top-level unit: X coordinate
## odd/even distinguish aisle sides; not necessary
##
tGROUPX = {
	0: 'ABC',
	1: 'DEF',    ## end of aisle 0
	2: 'GHI',
	3: 'JKL',    ## end of aisle 1
	4: 'MNO',
	5: 'PQR',    ## end of aisle 2
}
##
## Y coordinate (order within aisle) for each SKU
tGROUPY = {
	0: 'ADGJMP',
	1: 'BEHKNQ',
	2: 'CFILOR',
}
## ordering within groups: uniform distances -> cost
## aisle grouping from tGROUPX[], so tGROUPY[] only needs flat lists


## ordering frequency; does not need to be normalized
tFREQ = {
	'A': 400,
	'B': 300,
	'C': 50,
	'D': 600,
	'E': 400,
	'F': 100,

	'G': 800,
	'H': 1000,
	'I': 700,
	'J': 900,
	'K': 1000,
	'L': 700,

	'M': 500,
	'N': 200,
	'O': 50,
	'P': 300,
	'Q': 30,
	'R': 20,
}

## tables expanded to SKU-to-group and other lookup tables at runtime

## orders are represented by lists of [SKU, element] tuples
##
## individual ordering, collating identical SKUs etc. change
## as orders proceed through distribution


##----------------------------------------------------------------------------
## extract SKU-to-... lookup tables
##
def luts():
	sku2grp, sku2dist, sku2freq = {}, {}, []
			## 'dist' in this case is Y coordinate

	for g in tGROUPX:
		for s in tGROUPX[g]:                            ## list of SKUs
			if (s in sku2grp) and (sku2grp[s] != g):
				raise ValueError(f'reassigned [{s}] ' +
				                 'to different groups')
			sku2grp[s] = g


	for g in tGROUPY:
		for s in tGROUPY[g]:                            ## list of SKUs
			if (s in sku2dist) and (sku2dist[s] != g):
				raise ValueError(f'reassigned [{s}] ' +
				                 'within aisle')
			sku2dist[s] = g


		## turn relative frequencies into cumulative-probability list
		##
		## simulation purposes only!
		## [used only to generate random orders]
		##
	for s in tFREQ:
		if (not s in sku2dist) or (not s in sku2grp):
			raise ValueError(f'unknown SKU [{s}] may be ordered')
		##
		## SKUs, in decreasing relative-frequency order:
		## [using set(...) to eliminate duplicates]
		##
	for freq in sorted(set(tFREQ.values()), reverse=True):
		curr = list(sorted((s for s in tFREQ.keys()
		            if (tFREQ[s] == freq))))
					## all SKUs with this rel.frequency

		print(f'## _REL.FREQ {freq} { ",".join(curr) }')
		for s in curr:
			sku2freq.append([ s, tFREQ[ s ] ])

				## relative -> cumulative frequency
				## accumulate as current +prev. cumulative f
				##
			if len(sku2freq) > 1:
				sku2freq[-1][1] += sku2freq[-2][1]

	for c in sku2freq:
		print(f'## _CUMULATIVE.FREQ { c[0] } { c[1] }')

	print(f'## _FREQUENCY.TOTAL { sku2freq[-1][1] }')


	return sku2grp, sku2dist, sku2freq


##----------------------------------------------------------------------------
## turn SKU-to-position lookups into SKU-to-SKU cost lookups
##
## dists[ SKU1 ][ SKU2 ] = ...total cost between location of two SKUs...
##  next[ SKU1 ]         = [ dist1: [ neighbour1, neighbour2, ... ],
##                           dist2: [ neighbour, ... ],
##                           ... ]
##              adjacency information: neighbours in increasing-distance order
## 
def skus2distances(sku2grp, sku2dist):
	dists, delta = {}, {}

	if sku2grp.keys() != sku2dist.keys():
		raise ValueError('SKU grouping and distance lists differ')

	skus = sorted(sku2grp.keys())
	for si in enumerate(skus):                         ## (index, SKU ID)
		for d in skus[ si[0]+1: ]:                 ## SKU IDs > base ID
			s = si[1]
			v = 0

			##-----  warehouse-specific cost  --------------------

					## 'aisle coordinates' for both SKUs
			xs, ys = sku2grp[s], sku2dist[s]
			xd, yd = sku2grp[d], sku2dist[d]

				## Manhattan coordinates for traversal
				##
				## reminder: aisle_2N == aisle_2N+1 in cost
				## function (they are physically adjacent)
				##
			xdiff = abs((xs //2) - (xd // 2))

			ydiff = abs(ys - yd)

			c = vAISLE * xdiff + vROW * ydiff

			##-----  /warehouse-specific cost  -------------------

				## TODO: use version-portable set-default
			if not s in dists:
				dists[ s ] = {}
			if not d in dists:
				dists[ d ] = {}

				## not an adventure game: assume traversal
				## costs are symmetric
			dists[ s ][ d ] = c
			dists[ d ][ s ] = c

			##-----  /store mutual distances  --------------------

				## TODO: use version-portable set-default
			if not s in delta:
				delta[ s ] = { c: [] }
			if not c in delta[s]:
				delta[ s ][ c ] = []
			##
			if not d in delta:
				delta[ d ] = { c: [] }
			if not c in delta[d]:
				delta[ d ][ c ] = []
			##
			delta[ s ][ c ].append(d)
			delta[ d ][ c ].append(s)

			##-----  /append to SKU-to-distance list  ------------

			print(f'## _COST {s}->{d} {c}  ({xs},{ys})->' +
			      f'({xd},{yd})')

	for s in sorted(delta.keys()):
		for d in sorted(delta[s]):
			print(f'## _DIST {s}+{d}',
			      ", ".join(sorted(delta[s][d])))

	return dists, delta


##----------------------------------------------------------------------------
import random


##--------------------------------------
## return True with 'prob' parts-per-million probability
def ppm(prob):
	return prob < random.randint(0, 1000000)


##----------------------------------------------------------------------------
## 'typically distributied' random number of items ordered
##
def item2count(item):
	if ppm(750000):
		return 1

	if ppm(500000):
		return 2
	if ppm(500000):
		return 3
	if ppm(500000):
		return 4
	return 5


##--------------------------------------
## pick random entry based on [cumulative] relative-frequency statistics
## 'freq' MUST be [item, rel.frequency] in decreasing-frequency order
##
def random_item(freq):
	rn = random.randint(0, freq[-1][1] -1)

			## ordered list could be filtered MUCH more efficiently
			## please do not comment on this
			##
	i = list(i  for i in range(len(freq))  if (freq[i][1] >= rn))[0]
		
	return freq[i][0]


##--------------------------------------
## order a random number of items
##
## returns list of [item, count] in arbitrary order
## items MAY repeat; do not expect customers to collate
##
## supply 'reasonable' number of items if 0 is provided
##
def order_random(sku2freq, items=0):
	ord, seen = [], {}
		## 'seen' collects items already ordered
		## use it to _mainly_ (but not completely) eliminate duplicates

	if items == 0:
		items = random.randint(3, 8)

	for i in range(items):
		s = random_item(sku2freq)
		if (s in seen) and ppm(900000):
			continue

		count = item2count(s)
		ord.append([s, count])

		seen[s] = 1

	return ord


##--------------------------------------
## order is list of [SKU, count] tuples
##
def dump_order(o, msg=None):
	if msg:
		print(msg +' ', end='')

	print(', '.join(f'{i[0]} x{i[1]}'  if (i[1] >1) else  f'{i[0]}'
	                for i in o))


##--------------------------------------
## collate repeated items
## SKU order is unchanged, other than removing duplicates
##
## [I, 2], [K, 1], [I, 1]  ->  [I, 3], [K, 1]
##
def order2merge(o):
	res, total = [], {}

	for (s, count) in o:
		if not s in total:
			res.append(s)
			total[ s ] = 0
		total[ s ] += count

	return list([r, total[r]] for r in res)


##--------------------------------------
## merge 'o' order into batch
##
def order2batch(batch, order):
			## operate on local copy, w/o updating 'batch'
	res = batch[:]
	res.extend(order)

	return order2merge(res)


##----------------------------------------------------------------------------
## 'where' is current position (SKU) of batch
## 'order' MUST NOT be empty
##
## returns [SKU, cost] tuple, the cheapest one, or one of those if multiple
##
## special-case X->X transitions, so other stages do not need to filter
##
def nearest_sku(order, deltas, where):
	if not where in deltas:
		raise ValueError(f'distance mapping lacks SKU {where}')

	if order == []:
		raise ValueError('attempting to scan beyond end of order list')

	todo = list(i[0]  for i in order)           ## what to pick up in order

	diff, best = -1, None

			## find lowest cost destination in order from 'where'
			##
			## picks 'any of equal-cost best choices'
			## (we select alphabetic order for simplicity)
			##
			## TODO: store reversed index (just incremental scan)
			##
	for cost in sorted(deltas[ where ].keys()):
		dests = deltas[ where ][ cost ]

			## possible-destination SKUs we are interrested in

		dests = list(sorted(d  for d in dests
		                    if (d in todo) and (d != where)))
		if dests == []:
			continue

		diff, best = cost, dests[0]

		if len(dests) > 1:      ## trim multi-list to single, first SKU
			print(f'## ORDER.CHOICE {where}->' +
			      ",".join(dests) +f'[cost={cost}],pick={ best }')
		break

	if (diff < 0) or (best == None):
		raise ValueError(f'no transition/cost found from {where}')

	print(f'## NEAREST[{where}..{ best }]={ "+" if (diff >0) else "" }' +
	      f'{ diff }')

	return [best, diff]


##----------------------------------------------------------------------------
## special-case start position, removing any SKUs there immediately
##
## returns [aggregate cost, [route with incremental costs]] list
##
def order2cost(order, deltas, start=vSTART, msg=''):
	route, pos, total, seen = [], start, 0, {}
			## route collects [SKU, +cost] tuples

	todo = order2merge(order)

	dump_order(todo, f'## EVALUATE.{msg} '  if msg  else '## EVALUATE ')

			## do we need an SKU from 'start'?  remove right away
			## initial, zero-cost operation
			##
	if list(o  for o in todo  if (o[0] == start)):
		todo = list(o  for o in todo  if (o[0] != start))
		route.append([start, 0])

	seen[ start ] = 1

			## remove each SKU as they are collected
			## note that 'order' may not yet be sorted, so we
			## must filter upon each advance
			##
	while todo:
		nx, diff = nearest_sku(todo, deltas, pos)

		total += diff
		pos   =  nx
		seen[ nx ] = 1

		todo = list(o  for o in todo if (o[0] not in seen))
		route.append([nx, diff])

	return total, route


##----------------------------------------------------------------------------
if __name__ == '__main__':
	s2grp, s2dist, s2freq = luts()

	print('\n'.join(f'## _SKU {s} AT ({ s2grp[s] },{ s2dist[s] })'
	      for s in sorted(s2grp.keys())))

		## absolute positions; displacement costs
		##
	dists, deltas = skus2distances(s2grp, s2dist)

	batch, orders = [], []

	for b in range(4):                              ## construct test batch
		o = list(order_random(s2freq))
		dump_order(o, f'ORDER.RAW[{b}]')
		orders.append(o)

		dump_order(o, f'ORDER[{b}]')

		batch = order2batch(batch, o)

		dump_order(batch, f'BATCH.RAW[{b}]')

	print(f"BATCH.ELEMENTS={ len(orders) }")
	dump_order(batch, 'BATCH')

	bcost  = order2cost(batch, deltas, msg='BATCH')
	print('ROUTE.BATCH='+ (','.join((f'{ r[0] }(+{ r[1] })')
				       for r in bcost[1])))
	print('')

	ocosts = []
	for o in orders:
		ocosts.append(order2cost(o, deltas))
		print(f'ROUTE[{ len(ocosts) -1 }]='   +
		      (','.join((f'{ r[0] }(+{ r[1] })')
				for r in ocosts[-1][1])))
		print('')

	for b in enumerate(o[0] for o in ocosts):
		print(f"COST.ORDER[{ b[0] }]={ b[1] }")
	##
	nonb = sum(o[0] for o in ocosts)
	##
	print(f"COST.NOBATCH={ nonb }")
	print(f"COST.BATCH={ bcost[0] }")
	print(f"COST.BATCH.DELTA={ bcost[0] -nonb }")

