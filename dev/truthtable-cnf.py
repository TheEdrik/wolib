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
## please do not comment on splitting-through-string, or repeatedly
## evaluating expression in loop
##
## available functions:
##   AND, OR, NAND, NOR, XOR, XNOR
##   1OFN         (or 1-of-N)
##   MAX1OFN      (or MAX-1-of-N)
##   LESSTHAN     (or LESS-THAN)     -- compares N-bit combinations <= 'limit'
##   LESSTHAN-NZ  (or LESS-THAN-NZ)  -- ... 0 < N-bit combinations <= 'limit'
##   LT           2x N-bit values    -- A < B ?
##   LE           2x N-bit values    -- A <= B ?
##   DIFF         2x N-bit values    -- A != B ?
##                                   -- essentially, an OR of XORs
##   DIFF-NZ      2x N-bit values    -- A != B  or  A == 0  or  B == 0 ?
##                                   -- used when comparison must treat
##                                   -- 0 as unassigned/unknown (-> !different)
##
def truthtable(fn, n, vars='v', limit=0):
	fn   = fn.upper()
	is2x = ((fn == 'DIFF') or (fn == 'DIFF-NZ') or (fn == 'LT') or
	        (fn == 'LE'))

	if ((fn == 'LESSTHAN')    or (fn == 'LESS-THAN') or
	    (fn == 'LESSTHAN_NZ') or (fn == 'LESS-THAN-NZ')):
		if limit < 1:
			raise ValueError("upper limit must be >0")
		if limit >= (1 << n):
			raise ValueError(f"upper limit must be over {n} bits")

	if is2x:
		n += n

	for v in range(1 << n):
		vb0s = f'{ v :0{n}b}'
		vb   = list(int(b)  for b in vb0s)

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

							## compound functions
		elif (fn == '1OFN') or (fn == '1-OF-N'):
			r = 1  if (sum(vb) == 1)  else 0
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
		vb.append(r)

		print(" ".join(str(v) for v in vb))
	print('')
##
## see pack/dev/satcnf.py for current form


##============================================================================
## Quine McCluskey minimization of CNF truth table
##


##--------------------------------------
if True:
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

