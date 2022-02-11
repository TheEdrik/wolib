#!/usr/bin/python3

import random, fileinput, os, sys, itertools, math

##---  Sierpinski-curve, 2D <=> 1D mapping  ----------------------------------
## - use curve in 2^N square
##     25% +-------+-------+ 50%
##         | \    NNN    / |
##         |   \   |   /   |
##         |W    \ | /    E|
##         +W------+------E+
##         |W..../ | \    E|
##         |.../   |   \   |
##         |./    SSS    \ |
##      0% +-------+-------+ 75%
##         100%
## - recurse down to highlighted lower [S] half of W quadrant:
##     - S+E       -> recurse through +180 degree rotation (S->N; E->W)
##     - N         -> recurse through +90  degree rotation (N->W)
##     - W[N half] -> recurse through +45  degree rotation
##
## recursive descent into the lower half-triangle of the W quadrant
## (marked with dots)

vPOINTS   = 40         ## number of equidistant subdivisions of (0..1.0)


##--------------------------------------
def xy2idx(x, y):
	return f'{x}:{y}'


##--------------------------------------
## passes through val; potentially caching as well
##
def xy2cache(cache, x, y, val):
	if cache != None:
		idx = xy2idx(x, y)
		if not idx in cache:
			cache[ idx ] = val

	return val


##--------------------------------------
def emptycache():
	return {
		xy2idx(0, 0): 1,
		xy2idx(1, 1): 2,
		xy2idx(0, 1): 3,
		xy2idx(0, 2): 4,
		xy2idx(1, 2): 5,
		xy2idx(2, 2): 6,
	}


##----------------------------------------------------------------------------
## (x, y) from square grid of 2^N for N>=2 points per axis
##
def xy2sb(x, y, n, cache=None):
	total, plus, maxc = 0, [], 1 << n
	x0, y0 = x, y

	if (n < 2):
		raise ValueError(f'N ({n}) out of range')
	if (x < 0) or (x > maxc):
		raise ValueError(f'X ({x}) out of range (2^{n})')
	if (y < 0) or (y > maxc):
		raise ValueError(f'Y ({y}) out of range (2^{n})')

	if cache and xy2idx(x, y) in cache:
		return cache[ xy2idx(x, y) ]

	##----  only once: descent S+E -> N+W  -------------------------------

	if (y < x):
		plus.append([maxc, maxc])
		print(f'#r180 {x},{y} -> {maxc -x},{maxc -y}')
		x, y = maxc -x, maxc -y

	##----  possibly iterative: descend within N+W upper left triangle  --

	while (maxc > 2):
		print(f'2^N == {maxc}')

		if (y > maxc -x):
			plus.append([0, maxc])
			print(f'#r90 {x},{y} -> {maxc -y},{x}')
			x, y = maxc -y, x

		if (y > maxc //2):
			plus.append([maxc //2, maxc //2])
			print(f'#r45 {x},{y} -> {y -maxc //2},{maxc //2 -x}')
			x, y = y -maxc //2, maxc //2 -x

		maxc //= 2

	## ...descend into [0..2]x[0..2]

		## see also: emptycache()
	total = {
		'0,0': 1,
		'1,1': 2,
		'0,1': 3,
		'0,2': 4,
		'1,2': 5,
		'2,2': 6,
	}[ f'{x},{y}' ]
				## already set in emptycache()

		## ...total += sum(...plus...) == subt
	subtotals = 0

				## sum from sub-triangles
				## original order was descending
				##
	for px, py in reversed(plus):
		print(f'## ++{px, py}')

		if cache and (xy2idx(px, py) in cache):
			subt = cache[ xy2idx(px, py) ]
			print(f'## cache={ subt }')

		else:
			print(f'## recurse: {px},{py}')
			subt = xy2sb(px, py, n, cache=cache)

		subtotals += subt

	print(f'# X,Y={x0},{y0} ={total +subtotals} ({total} +{subtotals})')
	print()

	total += subtotals

	return xy2cache(cache, x0, y0, total)


##--------------------------------------
def digitsneeded(val):
	d = 0
	while ((val > 0) or ((val == n) and (n == 0))):
		val //= 10
		d += 1
	return d


##----------------------------------------------------------------------------
if __name__ == '__main__':
	for n in [6, 7, 8, 9, 10]:
		print(f'---2^{n} bits:--------------')

		res, val2xy, cache, maxval = [], {}, emptycache(), -1

		for x in range((1 <<n) +1):
			res.append([])
			for y in range((1 <<n) +1):
				s = xy2sb(x, y, n, cache)
				res[-1].append(s)
				maxval = max(maxval, s)

				if (s in val2xy):
					px, py = val2xy[s][0], val2xy[s][1]
					raise ValueError("identical mappings" +
					                 f"s={s} {x},{y} vs " +
					                 f"{px},{py}")
				val2xy[ s ] = [ x, y ]

		print('level-to-XY map:')
		for v in sorted(val2xy.keys()):
			x, y = val2xy[v][0], val2xy[v][1]
			print(f'  {v}: {x} {y}')

					## uniform-align columns of coordinates
		ndigits = digitsneeded(maxval)

		print('XY-to-level map:')
		print('## generated table, please do not modify it\n')
		print(f'tTABLE = [     ## {len(res)}x{len(res[-1])}')

		for r in res:
			print('\t[' +(', '.join(f'{v:{n}}' for v in r)) +', ],')

		print(f']')
		print('## /generated table')

		print(f'---/2^{n} bits--------------\n')

