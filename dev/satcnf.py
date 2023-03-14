#!/usr/bin/python3

## construct SAT-solver expressions for solving vehicle routing subproblems

import re, sys


##--------------------------------------
## please do not comment on splitting-through-string, or repeatedly
## evaluating expression in loop
##
## available functions:
##     AND, OR, NAND, NOR, XOR, XNOR
##     1OFN      (or 1-of-N)
##     MAX1OFN   (or MAX-1-of-N)
##     LESSTHAN  (or LESS-THAN)    -- compares N-bit combinations <= 'limit'
##
##     DIFFER                      -- feed even nr. of bits, used as 2x N/2
##                                 -- as nr1, nr2, respectively
##                                 -- evaluate nr1 != nr2
##     DIFFER-OR-0                 -- as with DIFFER, but true if
##                                 -- either nr1 or nr2 are all-0
##     DIFFER-AND-NOT-0            -- as with DIFFER, but false if
##                                 -- either nr1 or nr2 are all-0
##
## with cnf>0, outputs directly CNF-usable form, with first variable
## set to 'cnf'
##
def truthtable(fn, n, vars='v', limit=0, cnf=0):
	fn  = fn.upper()
	res = []

	if (fn == 'LESSTHAN') or (fn == 'LESS-THAN'):
		if limit < 1:
			raise ValueError("upper limit must be >0")
		if limit >= (1 << n):
			raise ValueError(f"upper limit must be over {n} bits")

	if (fn == 'DIFFER') or (fn == 'DIFFER-OR-0'):
		if n % 2:
			raise ValueError(f"DIFFER needs even nr. of bits")

	for v in range(1 << n):
		vb = list(int(b)  for b in f'{ v :0{n}b}')

		nr1, nr2 = vb[ :n//2 ], vb[ n//2: ]     ## 2x halves

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
			r = (v < limit)

		elif (fn == 'DIFFER'):
			r = (nr1 != nr2)

		elif (fn == 'DIFFER-OR-0'):
			nr1nz = max(nr1)
			nr2nz = max(nr2)
			r     = ((nr1 != nr2) and nr1nz and nr2nz)

		elif (fn == 'DIFFER-AND-NOT-0'):
			no0 = min(max(nr1), max(nr2))
			r   = ((nr1 != nr2) and no0)

		else:
			raise ValueError("unknown function")

		r = 1  if r  else 0            ## allow Boolean etc. from cases

		vb.append(r)

		if cnf > 0:
			vb = list((vi+cnf  if v else  -vi-cnf)
			          for vi, v in enumerate(vb))
		res.append(vb)

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
## return mapping table for string-to-int conversion for CNF specification
##
## inputs is all-numeric strings, standalone, or whitespace-separated clauses
## 'DDD' for True, '-DDD' for False values
##
## non-None 'values' is checked for already-assigned value; not updated
##
def satsolv_strings2ints(vars, values=None, first=1):
	res = {}

	for r in vars:
					## split each to sign ('-' or empty)
					## and base string
		_, curr = satsolv_str2ids(r.split())

		for id in curr:
			if values and (id in values):
				continue

			if not (id in res):
				res[ id ] = first
				first += 1
	return res


##-----------------------------------------
sNALL0 = 'NZ'                     ## suffix for not-all-(values-)zero +variable
sNALL1 = 'ALL1'                   ## suffix for all-(values-)one +variable


##-----------------------------------------
##
def satsolv_xor1_clauses(var1, var2, result, negate=False):
	if negate:                     ## X(N)OR only swap truth table polarity
		pol = [ ' ', '-', '-', ' ', ]
	else:
		pol = [ '-', ' ', ' ', '-', ]

	return [
		f' {var1}  {var2} { pol[0] }{ result }',
		f'-{var1}  {var2} { pol[1] }{ result }',
		f' {var1} -{var2} { pol[2] }{ result }',
		f'-{var1} -{var2} { pol[3] }{ result }',
	]


##-----------------------------------------
## XOR of two bits; 'negate' chooses XNOR
##
## sample: A; B; N = A ^ B
##     1) A | B | not(N)             N -> (A | B)
##     2) not(A) | N       together: (A | B) -> N
##     3) not(B) | N
##
## None 'result' auto-assigns variable name
## returns list of clauses, name of final variable, + comment
##
def satsolv_xor1(var1, var2, result=None, negate=False):
	cls = []

	if result == None:
		negstr = 'n'  if negate  else ''
		result = f'{ var1 }_{ negstr }x_{ var2 }'

	cls = satsolv_xor1_clauses(var1, var2, result, negate=negate)

##	if negate:                     ## X(N)OR only swap truth table polarity
##		pol = [ ' ', '-', '-', ' ', ]
##	else:
##		pol = [ '-', ' ', ' ', '-', ]
##
##	cls.extend([
##		f' {var1}  {var2} { pol[0] }{ result }',
##		f'-{var1}  {var2} { pol[1] }{ result }',
##		f' {var1} -{var2} { pol[2] }{ result }',
##		f'-{var1} -{var2} { pol[3] }{ result }',
##	])
	negstr = 'NOT'  if negate  else ''

	return cls, result, f'{ result } := { negstr }({var1} XOR {var2})'


##-----------------------------------------
## NAND, for two bits
##
## sample: A; B; N = not(A & B)
##     1) not(A) | not(B) | not(N)
##     2)      A | N
##     3)      B | N
##
## None 'result' auto-assigns variable name
## returns list of clauses + comment
##
## TODO: merge with AND
##
def satsolv_nand1(var1, var2, result=None):
	cls  = []

	if result == None:
		result = f'{ var1 }_nn_{ var2 }'

			## placeholders, for column alignment
	v1p = ' ' * (len(var1) +1)
	v2p = ' ' * (len(var2) +1)

	cls.extend([
		f'-{var1} -{var2} -{result}',
		f' {var1} { v2p }  {result}',
		f' {var2} { v1p }  {result}',
	])

	return cls, result, f'{ result } := ({var1} NAND {var2})'


##-----------------------------------------
## sample: A; B; N = A | B
##     1) A | B | not(N)             N -> (A | B)
##     2) not(A) | N       together: (A | B) -> N
##     3) not(B) | N
##
## None 'result' auto-assigns variable name
## returns list of clauses, name of final variable, + comment
##
def satsolv_or(base, vars, result=None):
	cls = []
	v   = sorted(vars)

	if result == None:
		result = base + sNALL0

	all = list((base +b)  for b in  v)
	all.append(f'-{ result }')
		##
	cls.append( " ".join(all) )                   ## A | B | not(N)

	terms = list((base +b)  for b in v)

	cls.extend((f'-{ t } { result }')  for t in terms)

	return cls, result, f'{ result } := (' +(" OR ".join(terms)) +')'


##-----------------------------------------
## sample: A; B; N = A & B
##     1) not(A) | not(B) | N            N -> (A & B)
##     2) A | not(N)           together: (A & B) -> N
##     3) B | not(N)
##
## None 'result' auto-assigns variable name
## returns list of clauses + comment
##
def satsolv_and(base, vars, result=None):
	cls  = []
	v    = sorted(vars)

	if result == None:
		result = base + sNALL1

	all = list((f"-{ (base +b) }")  for b in  v)
	all.append(result)
		##
	cls.append( " ".join(all) )                   ## not(A) | not(B) | N

	terms = list((base +b)  for b in v)

	cls.extend((f'{ t } -{ result }')  for t in terms)

	return cls, result, f'{ result } := (' +(" AND ".join(terms)) +')'


##----------------------------------------------------------------------------
## input restricted to string of all-0/1 integers of value V
##
## return broken down to consecutive regions of all-identical elements
##     '11010' -> [ '11', '0', '1', '0' ]
##
def arr2consective(vbin):
	arr = [ ch.group(0)  for ch in  re.finditer(r'(\d)\1*', vbin) ]

	return arr


##--------------------------------------
## decomposed versions for small N, with don't care trailing bits marked:
##
##                               v--- nr of comparison windows if >0
##    i= 1  ib=    1  ib'=    1           -- never above
##    i= 2  ib=   10  ib'=   10  2
##    i= 3  ib=   11  ib'=   11           -- never above
##    i= 4  ib=  100  ib'=  100  2
##    i= 5  ib=  101  ib'=  10.  2
##    i= 6  ib=  110  ib'=  110  2
##    i= 7  ib=  111  ib'=  111           -- never above
##    i= 8  ib= 1000  ib'= 1000  2
##    i= 9  ib= 1001  ib'= 100.  2
##    i=10  ib= 1010  ib'= 1010  4
##    i=11  ib= 1011  ib'= 10..  2
##    i=12  ib= 1100  ib'= 1100  2
##    i=13  ib= 1101  ib'= 110.  2
##    i=14  ib= 1110  ib'= 1110  2
##    i=15  ib= 1111  ib'= 1111           -- never above
##    i=16  ib=10000  ib'=10000  2
##    i=17  ib=10001  ib'=1000.  2
##    i=18  ib=10010  ib'=10010  4
##    i=19  ib=10011  ib'=100..  2
##    i=20  ib=10100  ib'=10100  4
##    i=21  ib=10101  ib'=1010.  4
##    i=22  ib=10110  ib'=10110  4
##    i=23  ib=10111  ib'=10...  2
##    i=24  ib=11000  ib'=11000  2
##    i=25  ib=11001  ib'=1100.  2
##    i=26  ib=11010  ib'=11010  4
##    i=27  ib=11011  ib'=110..  2
##    i=28  ib=11100  ib'=11100  2
##    i=29  ib=11101  ib'=1110.  2
##    i=30  ib=11110  ib'=11110  2
##    i=31  ib=11111  ib'=11111      -- never above


##--------------------------------------
## N-bit variable list, assumed big-endian V value as v0..v[N-1]
## construct expression for ...N-bit uint... <= maxv
##
## returns (control variable, list of clauses (possibly empty), comment)
##     None control variable AND empty clause -> no comparison needed
##
## TODO: restricted to fixed compositions
## sanity check that maxv is has minimal nr. of bits
##
def satsolv_le(vars, maxv):
	cls   = []
	mvbin = f'{ maxv :b}'           ## implicit 0-stripping, so [0]==1

	if len(vars) != len(mvbin):
		raise ValueError("CNF: inconsistent <= set size")

	arr = arr2consective(mvbin)
	assert(arr[0][0] == '1')        ## see above, 1st region always all-0

	if len(arr) == 1:
		return None, [], ''       ## 2^N -1:  V is never > 2^N-1

				## '11011' -> [ '11', '0', '11' ]
				## value is always >= MS region, which is all-1
				##
				## hierarchical decoding:
				##   - all-1 region: is value < mask?
				##       ->  value NOT all-1 (AND)  ->  V < L
				##   - all-0 region: is value > mask?
				##       ->  value not all-0 (OR)  ->  V > L
				##   - any other case: proceed to lower-valued
				##     bits
				##
				## regions alternate
				##
				## single-bit regions trivially simplify,
				## use individual bits and skip AND/OR

				## trailing all-1 region may be dropped, since
				## it never decides: V <= L  against all-1 L ->
				## higher-order bits must decide before
	if (arr[-1][0] == '1'):
		arr.pop(-1)
				## -> nr of regions to compare is even
				## (1 -> 0 -> ... -> 1)  was even, trailing
				##  1 has been dropped

	if (len(arr) > 3):
		raise ValueError("check back when implemented...")

	bdone = 0               ## 'bits done': processed, MS to LS
	bvars = vars[:]         ## allow modifying local list

	for r in arr:
		currbits = len(r)
		currvars, bvars = bvars[ :currbits ], bvars[ currbits: ]

		if currbits == 1:
						## ...single-bit term...
			pass

		else:
						## ...process rest...
			pass

		bdone += currbits

	return None, cls, ''


##-----------------------------------------
## given 2x N IDs (for two N-bit IDs) and a max-element count, return
## clauses which encode True if:
##   (1) any of the N-bit inputs is all-zero
##   (2) the N-bit unsigned ints differ
## in other words, 'nonzero-differ(v1, v2)'
##
## returns (list of clauses); comment
##
## encode only to strings, require subsequent string-to-variable(index) mapping
##
## comparison is used when cross-checking assigned times, each 'vars' is:
##   dXX tYY z0..z(N-1)    delivery XX, time window YY, vehicle ZZ delivers
##                         -> delivery constraint is: if both deliveries
##                            are assigned, MUST NOT be the same vehicle
##                            (since they could not traverse in time)
##
## 'base' stores dXX tYY terms, or any common prefix
## define 'base' as variable if any of the 'base+vars' bits are True
##
def satsolv_nzdiffer_n(base1, base2, vars1, vars2=[]):
	cls = []

	v1 = vars1[:]

	if vars2 == []:
		v2 = v1
	else:
		if len(v1) != len(v2):
			raise ValueError(f"mismatched sizes ( {len(v1) } " +
				f" != { len(v2) })")

	cls, _ = satsolv_or(base1, v1)
	cls.extend( satsolv_or(base2, v2)[0] )

	for c in cls:
		print(f'  CLAUSE={ c }')

## TODO: comparison

	return cls, ''


##-----------------------------------------
## Return 'commander variables', newly added (commander) variables,
## related additional clauses, and comments documenting the collection.
##
## The first element of the commander-variable array is true if and only
## exactly one of 'vars' (variable-name) inputs is True.
##
## commander variables are named 'CMDR...'; prefix MUST NOT be used by others
##
## 'nr' is the number of defined variables, incl. current inputs
##
## see
## Kliebert, Kwon: Efficient CNF encoding for selecting 1 of N objects,
## www.cs.cmu.edu/~wklieber/papers/
##     2007_efficient-cnf-encoding-for-selecting-1.pdf
## [accessed 2023-02-24]
##
def satsolv_1n(vars, nr=0):
	if vars == []:
		raise ValueError("called with empty variable list")

	if len(vars) == 1:
		return vars[0], [], [], ''

		## set newvar and cls to newly added variables + their clauses
		## lf, rg are command variables of layers below

	if len(vars) == 2:
		lf, rg, newvar, addval, cls = vars[0], vars[1], [], 0, []

	else:
		half = len(vars) // 2
		lf, newvar, cls, _ = satsolv_1n(vars[    :half], nr)
		rg,  nvar2, cl2, _ = satsolv_1n(vars[half:    ], nr+len(newvar))

		newvar += nvar2
		cls    += cl2

	cmd = f'CMDV{ nr +len(newvar) +1 }'
	newvar.insert(0, cmd)

	cls.extend(satsolv_xor1_clauses(lf, rg, cmd))
##	cls.extend([                         ## truth table for "{lf} XOR {rg}"
##		f' {lf}  {rg} -{cmd}',
##		f'-{lf}  {rg}  {cmd}',
##		f' {lf} -{rg}  {cmd}',
##		f'-{lf} -{rg} -{cmd}',
##	])

	varlist = ",".join(vars)

	return cmd, newvar, cls, f'1-of-N: ({ cmd }) for ({ varlist })'


##-----------------------------------------------------------
def nof1(n):
	vars = list(f"v{ s :06}" for s in range(1, n+1))
	top, nvars, cls, cmt = satsolv_1n(vars)

	cls.append(f'{top}')

	cr = satsolv_strings2ints(cls)

	clauses = []            ## integer-mapped form

	for c in cls:
		signs, curr = satsolv_str2ids(c.split())
		ints = list(cr[c]  for c in curr)

		print("c " + (" ".join(f"{ sv }{ cv }[{ iv }]"
			for sv, cv, iv  in zip(signs, curr, ints)))
			+ " 0")

		clauses.append(
			" ".join(f"{sv}{iv}"  for sv, iv  in zip(signs, ints))
		+" 0")

	print(f'p cnf { len(cr) } { len(clauses) }')

	print('\n'.join(clauses))


##-----------------------------------------------------------
if __name__ == '__main__':
	print(satsolv_and("base", [ "A", "B", "C", ]))
	print(satsolv_and("base", [ "A", "B", "C", ], result='AND_ABC'))
	print(satsolv_or("base", [ "A", "B", "C", ]))
	print(satsolv_or("base", [ "A", "B", "C", ], result='OR_ABC'))
	print(satsolv_xor1("A", "B", result='XOR_AB'))
	print(satsolv_xor1("A", "B"))
	print(satsolv_xor1("A", "B", result='XNOR_AB', negate=True))
	print(satsolv_xor1("A", "B", negate=True))
	print(satsolv_nand1("A", "B", result='NAND_AB'))
	print(satsolv_nand1("A", "B"))
	print(satsolv_le([ "v0", "v1", "v2", "v3", ], 15))
	print(satsolv_le([ "v0", "v1", "v2", "v3", ], 9))
	print(satsolv_le([ "v0", "v1", "v2", "v3", "v4", ], 23))

	print(" ".join(str(v) for v in truthtable('AND',  4)))
	print(" ".join(str(v) for v in truthtable('OR',   4)))
	print(" ".join(str(v) for v in truthtable('NAND', 4)))
	print(" ".join(str(v) for v in truthtable('NOR',  4)))
	print(" ".join(str(v) for v in truthtable('XOR',  4)))
	print(" ".join(str(v) for v in truthtable('XNOR', 4)))
	print(" ".join(str(v) for v in truthtable('XOR',  4, cnf=1)))
	print(" ".join(str(v) for v in truthtable('LESS-THAN', 5, limit=24)))
	print(" ".join(str(v) for v in truthtable('LESS-THAN', 5, limit=24, cnf=1)))
	print(" ".join(str(v) for v in truthtable('DIFFER', 8)))
	print(" ".join(str(v) for v in truthtable('DIFFER-OR-0', 8)))
	print(" ".join(str(v) for v in truthtable('DIFFER-AND-NOT-0', 8)))
	print(" ".join(str(v) for v in truthtable('DIFFER-AND-NOT-0', 10)))

	sys.exit(0)
	print(satsolv_nzdiffer_n("d31t11", "d44t22",
	      	             [ "z0", "z1", "z2", "z3", "z4" ]))

	nof1(256)

