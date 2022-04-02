#!/usr/bin/python3

##--------------------------------------
## is (x, y) within polygon?
## count rays cast from (x, y) to (inf, y): how many sections
## does it intersect?
##
## border is list of [x1, y1, y2, x2, minx, maxx, miny, maxy] tuples
## minx..maxy: entries are redundant since bounding rectangles are
## checked repeatedly when used in a loop
##
def is_inside(x, y, border):
	crosses = 0

	for b in border:
		minx = None

		if len(b) == 4:
			bx1, by1, bx2, by2 = b
			minx, miny = min(bx1, bx2), min(by1, by2)
			maxx, maxy = max(bx1, bx2), max(by1, by2)
		elif len(b) == 8:
			bx1, by1, bx2, by2, minx, maxx, miny, maxy = b
		else:
			raise ValueError("invalid boundary segment")

		if (x < minx) or (x > maxx) or (maxy < y):
			continue

		if (y < miny) and (minx <= x <= maxx):
			crosses += 1
			continue

				## please do not comment on float= comparisons
				## we do not really care about points
				## near the boundary

		## TODO: use an exception-free, stable formula here
		##
		##                    (bx2, by2) = B2
		##           +--------+
		##           |      / |
		##           |     /  |
		## (x, y) -> | X  /   |    X <- (2bx2, y)
		##           |   /    |
		##           |  /     |
		##           | /      |
		##           +--------+
		##  (bx1, by1) = B1
		##
		## intersect B2-B1 with (x,y) -> (2bx2, y)
		## the latter is always outside (B1, B2) bounding rectangle
		## specialized for delta.y == 0 for right-of-(x,y) segment
		##
		## p -> p+r
		## q -> q+s
		## intersection:
		##   p + t * r = q + u * s
		##   u = (q - p) x r / (r x s)

				## (approx.) angle(x,y) vs. angle(segment)

		axy = 90.0  if (bx1 == bx2)  else (  y -x  ) / (bx2 -bx1)
		asg = 90.0  if (bx1 == x  )  else (by2 -by1) / (  x -bx1)
		if axy >= asg:
			crosses += 1

	return (crosses & 1)


##---------------------------------------------
## turn input into k bytes of uniform-random (PRF) output, returned as bytes
## bytecount(output) == bytecount(maxn)
##
## DOES NOT MOD-REDUCE etc. output to be modn-based
##
## output is leading bytes of:
##    hash(...input...)
##    hash(...input... || x00000000)
##    hash(...input... || x00000001)
##    ...
##    hash(...input... ||  BE32(N) )
## ...if output needs N+2 blocks of 512-bit output (with hash=SHA512)
##
def seed2prf(seed, bits):
	if (bits < 1):
		raise ValueError("invalid PRF-output size")

	blks = (bits +512 -1) //512
					## excluding initial, unpadded block

	r = hashlib.sha512(seed).digest()

	for i in range(blks-1):
		post = i.to_bytes(32 // 8, byteorder='big')
		r += hashlib.sha512( seed +post ).digest()

	return r[ : (bits +7) //8 ]


##--------------------------------------
## generate points within normalized polygon
##
def points_inside_polygon(border, n=1000):
	deterministic = True
	seed0 = -1 
	pts   = []

	brd, prevx, prevy = [], border[0][0], border[0][1]
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

	while (len(pts) < n):
		seed0 += 1

		if deterministic:
			seedx = (seed0 +i+i  ).to_bytes(64//8, byteorder='big')
			seedy = (seed0 +i+i+1).to_bytes(64//8, byteorder='big')

			x = int.from_bytes(seed2prf(seedx, 64), 'big')
			y = int.from_bytes(seed2prf(seedy, 64), 'big')
		else:
			x, y = random.randint(0, 1<<64), random.random(0, 1<<64)

		x /= (1 << 64)
		y /= (1 << 64)

		if not is_inside(x, y, border):
			continue

##		print(f'{x:.06}\t{y:.06}')
		pts.append([x, y])

	return pts


##--------------------------------------
def bitcount(w):
	n = 0
	while (w >= (1 << 32)):
		w >>= 32
		n += 32
	while (w > 0):
		w >>= 1
		n += 1
	return n

