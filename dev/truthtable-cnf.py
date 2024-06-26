#!/usr/bin/python3

##--------------------------------------
## (1) generate truth tables
## (2) turn truth tables into CNF forms for use as SAT solver input


import vt, sys, math, hashlib, re, fileinput, random, os, vttest
import itertools


##--------------------------------------
## turn 0/1/Boolean input to printable string
def vals2strs(v):
	v2 = []
	for vals in v:
		v2.append(list(str(vc)  for vc in vals))

	return v2


##--------------------------------------
## returns string + int form (all 0/1 or equivalent)
##
def int2bits(v, bits):
	vb0s = f'{ v :0{bits}b}'
	vb   = list(int(b)  for b in vb0s)

	return vb0s, vb


##--------------------------------------
tOPR_2x = [
	'DIFF', 'DIFF-NZ', 'LT', 'LE', 'ADD', 'ADD_NC', '1OFN-2X',
]


##--------------------------------------
## please do not comment on splitting-through-string, or repeatedly
## evaluating expression in loop
##
## available functions:
##   AND, OR, NAND, NOR, XOR, XNOR
##   1OFN         (or 1-of-N)
##   1OFN-X2      two instances of 1-of-N
##   MAX1OFN      (or MAX-1-of-N)
##   LESSTHAN     (or LESS-THAN)     -- compares N-bit combinations <= 'limit'
##                                   -- limit is constant
##   LESSTHAN-NZ  (or LESS-THAN-NZ)  -- ... 0 < N-bit combinations <= 'limit'
##   LT           2x N-bit values    -- A < B ?
##   LE           2x N-bit values    -- A <= B ?
##   DIFF         2x N-bit values    -- A != B ?
##                                   -- essentially, an OR of XORs
##   DIFF-NZ      2x N-bit values    -- A != B  or  A == 0  or  B == 0 ?
##                                   -- used when comparison must treat
##                                   -- 0 as unassigned/unknown (-> !different)
##   SUM          N bits -> ceil(log2(N)) bits
##   ADD          2x N bits -> N +1
##   ADD_NC       2x N bits -> N, ignoring carry
##
def truthtable(fn, n, vars='v', limit=0):
	fn   = fn.upper()
	is2x = (fn in tOPR_2x)

	if ((fn == 'LESSTHAN')    or (fn == 'LESS-THAN') or
	    (fn == 'LESSTHAN_NZ') or (fn == 'LESS-THAN-NZ')):
		if limit < 1:
			raise ValueError("upper limit must be >0")
		if limit >= (1 << n):
			raise ValueError(f"upper limit must be over {n} bits")

	if is2x:
		n += n

	for v in range(1 << n):
		vb0s, vb = int2bits(v, n)

		if is2x:
			vms, vls = vb0s[ : n//2 ], vb0s[ n//2 : ] ## most+least
			vb,  v2b = vb[ : n//2 ],   vb[ n//2 : ]

		if fn == 'XOR':
			r = sum(vb) & 1
		elif fn == 'XNOR':
			r = 1 - (sum(vb) & 1)
		elif fn == 'OR':
			r = max(vb)
		elif fn == 'AND':
			r = min(vb)
		elif fn == 'NAND':
			r = 1 - min(vb)
		elif fn == 'NOR':
			r = 1 - max(vb)
		elif fn == 'SUM':
			r = int2bits(sum(vb), n.bit_length())[1]

		elif (fn == 'ADD') or (fn == 'ADD_NC'):
			r = int2bits(sum(vb), n.bit_length())[1]
## TODO: non-carry addition variant

							## compound functions
		elif (fn == '1OFN') or (fn == '1-OF-N'):
			r = 1  if (sum(vb) == 1)  else 0
		elif (fn == '1OFN-2X') or (fn == '1-OF-N-2X'):
			r = 1  if (sum(vb) == sum(v2b) == 1)  else 0

		elif (fn == 'MAX1OFN') or (fn == 'MAX-1-OF-N'):
			r = 1  if (sum(vb) <= 1)  else 0
		elif (fn == 'LESSTHAN') or (fn == 'LESS-THAN'):
			r = 1  if (v < limit)  else 0
		elif (fn == 'LESSTHAN-NZ') or (fn == 'LESS-THAN-NZ'):
			r = 1  if (0 < v < limit)  else 0

		elif (fn == 'LT'):
			r = 1  if (vms < vls)  else 0
		elif (fn == 'LE'):
			r = 1  if (vms <= vls)  else 0
		elif (fn == 'DIFF'):
			r = 1  if (vb != v2b)  else 0
		elif (fn == 'DIFF-NZ'):
			r = 1  if ((vb != v2b) or
					(min(max(vb), max(v2b)) == 0))  else 0
		else:
			raise ValueError("unknown function")

		if is2x:
			vb.extend(v2b)

		if isinstance(r, list) or isinstance(r, tuple):
			vb.extend(r)
		else:
			vb.append(r)

		print(" ".join(str(v) for v in vb))
	print('')
##
## see pack/dev/satcnf.py for current form


##============================================================================
if True:
#	bits = 8
#	truthtable('sum', bits)
#	sys.exit(0)

	bits = 8
	if 'BITS' in os.environ:
		bits = int(os.environ['BITS'])

	truthtable('1OFN', bits)
	sys.exit(0)

	## comparisons
	if 'LIMIT' in os.environ:
		limit = [ int(os.environ['LIMIT']) ]
		bits  = limit[0].bit_length()
	else:
		limit = range(1, 1 << bits)

	truthtable('DIFF-NZ', bits)

	sys.exit(0)
##------------------------------------
## TODO: mode selection
	for i in limit:
		if len(limit) > 1:
			print(f'## ...[{ i.bit_length() } bits] < {i}')

		truthtable('less-than', i.bit_length(), limit=i)
	sys.exit(0)

	truthtable('1-of-n', bits)
	sys.exit(0)

	truthtable('diff-nz', bits)
	sys.exit(0)

	truthtable('xor',  3)
	truthtable('xnor', 3)
	truthtable('and',  3)
	truthtable('or',   3)
	truthtable('nand', 3)
	truthtable('nor',  3)
	truthtable('1-of-n',     4)
	truthtable('max-1-of-n', 4)
	truthtable('less-than',  5, limit=17)
	truthtable('less-than',  5, limit=24)
	truthtable('less-than-nz', 5, limit=24)
	truthtable('le', 3)
	truthtable('le', 4)
	truthtable('le', 5)
	truthtable('lt', 3)
	truthtable('lt', 4)
	truthtable('lt', 5)
	truthtable('diff', 3)
	truthtable('diff', 4)
	truthtable('diff', 5)
	truthtable('diff-nz', 3)
	truthtable('diff-nz', 4)
	truthtable('diff-nz', 5)
	sys.exit(0)

