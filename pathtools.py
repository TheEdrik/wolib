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

