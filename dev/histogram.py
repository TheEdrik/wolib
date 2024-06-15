#!/usr/bin/python3

## data with given cumulative density function


import vt, re, sys, os, re, fileinput, random


##----------------------------------------------------------------------------
def all_uints(lines):
	arr = []
	for l in lines:
		arr.extend(int(v)  for v in re.findall('\d+', l))

	return arr


##--------------------------------------
def approx_histogram(table, elems, pct=0, ppm=0, minval=1):
				## note: random.sample() returns list, but
				## it selects unique elements
				## allow repeated selection (explicit loop)

	e = [ random.choice(table)  for i in range(elems) ]

	return [ max(minval, i)  for i in e ]


##--------------------------------------
if True:
	arr = [ l.decode('utf-8')
	        for l in open(sys.argv[1], 'rb').read().split(b'\n') ]
	arr = all_uints(arr)

	seedmask = (1 << 160) -1

	if 'SEED' in os.environ:
		seed = int(os.environ[ 'SEED' ], 0) & seedmask
	else:
		seed = random.randint(1, seedmask)

	for i in range(4):
		print(f'## SEED x{ seed :0{ seedmask.bit_length() //4 }x}')
		random.seed(seed)

		n     = random.randint(1, 64)
		elems = approx_histogram(arr, elems=n)
		fmt   = f'{ max(3, vt.log10(n)) }'

		for ei, e in enumerate(elems):
			print(f'{ e },1,unit{ ei +1 :0{ fmt }}')
		print()

		seed += 1
		seed &= seedmask

	sys.exit(0)

