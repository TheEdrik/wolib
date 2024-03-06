#!/usr/bin/python3

# generate SAT expressions for pack/solver
#
# 'template' option outputs a compressed template, a list of variable IDs,
# a structure which lists 'virtual' register numbers which one can then
# map onto actual SAT variables. See 'Template representation' below.
#
# template-generating options
#   OR         OR(...)
#   OR.FORCE   OR(...), forcing result to True
#   AND
#   AND.FORCE  AND(...), forcing result to True
#   1OFN       1-of-N, forced to be True
#   1OFN.VAR   1-of-N, return result in variable (not forced)
#   C          generate C of all templates
#   SUM        N inputs, each [0, M]; return their sum
#   NEQ0       2x N-bit inputs (1) at least one is all-0 (2) N-bit values differ
#
# env. control
#   MAXBITS    if set (MUST be multiple of 8), any template which
#              requires wider bitcount raises exception
#   UNIT       force entries to minimum width (bits) if >0
#
# Author: Visegrady, Tamas  <tamas@visegrady.ch>


# multi-expression tables are either condensed to the following form:
#   const uintNN_t [][] = {
#     { AAA,BBB,CCC,DDD ...clauses... },
#       ^^^ header[ vTEMPLATE_HDR_ENTRIES ]:
#         (1) nr. of input variables (V)
#         (2) nr. of added/intermediate variables (A)
#         (3) nr. of clauses
#         (4) max nr. of variables in worst-case clause (excl. terminating 0)
#     }
#
# OR they are flattened to a single list of uniform-sized units, and
# an additional index is generated. see bin2table.py


sSATPREFIX  = 'SAT='      ## common prefix for data applicable to SAT solvers
sSATCOMMENT = '## SAT='   ## SAT-related comment, for our own tracing
sSAT_CONSTR_END = ' 0'    ## terminate [term list of] constraint
sSAT_2ND_VAR    = 'NV'    ## prefix for secondary SAT (CNF) variables
sSAT_SYM_PREFIX = 'RAW='  ## prefix for clauses which are stored as strings,
                          ## only mapped to integer indexes in the end
                          ## DIMACS CNF: "1 2 -3 0"
                          ## 'raw' CNF:  "D1 D2 -D3"

import os, textwrap, sys, math, itertools, re, copy
from functools import cache                   ## memoization


##=====  Utilities  ==========================================================
## integer log-10, for positive input
## please do not mention inefficiency: we call with 1/2-digit limits
##
def log10(n):
	if (n <= 0):
		raise ValueError("log10() out of range")
	rv = 0
	while n:
		n //= 10
		rv += 1
	return rv


##-----------------------------------------
def next_power2(n):
	if (n <= 0):
		return 0
	elif n > 32:
		return 64
	elif n > 16:
		return 32
	elif n > 8:
		return 16
	else:
		return 8


##--------------------------------------
def allpairs(vars):
	return itertools.combinations(vars, 2)


##--------------------------------------
## memoize identical-input combinations
##
tTEMPLATE = []


##============================================================================
## Template representation
##
## Templates operate on a predefined number of inputs (N), generally
## add variables of their own (M), and add clauses combining the two.
## There are two possible representations, one listing symbolic
## variable names, and one listing only variable indexes.
##
## TODO: standardize 'inputs' usage
##
## Symbolic template:
##   { 'descr':    ...comment...
##     'inputs':   [ ...list of input variables... ],     ## N entries
##     'add.vars': [ ...list of new variables... ],       ## M entries
##     'nr.outputs': ...         ## number of output variables, at end
##                               ## of input|added, if any are added
##                               ##
##                               ## possible 0: if condition is forced,
##                               ## no variable is returned (it is a fixed
##                               ## result, not really a useful variable)
##     'outputs':  [ ...list of result variable indexes... ],
##     'clauses': [
##       [ clause1... ]
##       [ clause2... ]
##       ...
##                   ## clauses may use -N-M .. -1, 1 .. N+M
##                   ## no other variable indexes MAY be referenced
##                   ##
##                   ## assume [1 .. N] are original inputs; [N+1 .. N+M]
##                   ## are implicit added variables
##     ]
##     'fixed': {
##       True:  [ ... ]     ## known, fixed variables
##       False: [ ... ]
##     }
##     'nr.clauses': ...         ## redundant; for debug convenience
##   }
##
## Numeric template:
##   { 'descr':    ...comment...
##     'inputs':   [ ...list of input variable indexes... ],     ## N entries
##     'outputs':  [ ...list of result variable indexes... ],
##     'add.vars': M,            ## number of new variables, incl. outputs
##     'nr.outputs':             ## number of output variables, the
##                               ## first among 'add.vars', if any
##                               ##
##                               ## possible 0: if condition is forced,
##                               ## no variable is returned: it is a fixed
##                               ## result, not really a useful variable.
##     'clauses': [
##       [ clause1... ]
##       [ clause2... ]
##       ...
##                   ## clauses may use -N-M .. -1, 1 .. N+M
##                   ## no other variable indexes MAY be referenced
##     ]
##     'fixed': {
##       True:  [ ... ]     ## known, fixed variables
##       False: [ ... ]
##     }
##     'nr.clauses': ...         ## redundant; for debug convenience
##   }
##
## TODO: sub-structure; we have too many identical fields
##
## in both forms, assume [1 .. N] are original inputs; [N+1 .. N+M] are
## implicit added variables
##
## 'in.base' and 'add.base', when >0, indicate template has been
## rebased: input and additional-variable index starts at >0
##
## clauses' ordering conveys some idea about any hierarchical
## problem decomposition; there is no real implied order.

## Template summary
##
## when parsing multi-template limits, the following summary struct is
## returned:
## {
##   'units':     nr. of units in this template
##   'unit.bits': nr. of bits needed to represent worst-case entry
## }


##--------------------------------------
## empty construct for SAT solver aux. data
##
def template0(descr='UNDEFINED', inputs=0, in_base=0):
	return {
		'descr':      descr,
		'inputs':     inputs,
		'outputs':    [],
		'add.vars':   0,
		'nr.outputs': 0,             ## if >0, N variables are outputs
		'result':     0,             ## index if >0; TODO: multi-valued
		'in.base':    in_base,
		'add.base':   0,
		'clauses':    [],
		'nr.clauses': 0,
		'fixed':      {
			True:  {},
			False: {},
		},
		'comments':   [],
	}


##--------------------------------------
## update any dependent variables
def template_sync(t):
	t[ 'nr.clauses' ] = len(t[ 'clauses' ])


##--------------------------------------
def template_assertions(t):
	if t[ 'add.vars' ] < t[ 'nr.outputs' ]:
		raise ValueError("returning too many derived variables")
## TODO: clause cross-check


##--------------------------------------
def ints2xdigits(arr, xdigits):
	return [ f'0x{ v :0{ xdigits }x}'  for v in arr ]


##--------------------------------------
## integer-to-hex.digit-bitcount
##
def ints2xbits(arr, xbits):
	xdigits = (xbits +3) // 4
	return ints2xdigits(arr, xdigits)


##--------------------------------------
## recurring (diags) step: list all clauses in verbose+readable form
##
def list_clauses(cls, indent=2):
	for ci, c in enumerate(cls):
		print(f"## { ' ' * indent } C[{ ci+1 }] { c }")


##--------------------------------------
## template header, fixed units up front
##   - numeric result with 'fmtbits' 0
##   - string-formatted with 'fmtbits' > 0
##
def template2hdr(t, fmtbits=0, comment=True):
	vars, addl, cls = t[ 'inputs' ], t[ 'add.vars' ], len(t[ 'clauses' ])
	maxcvars = max(len(c) for c in t[ 'clauses' ])

	res = [ vars, addl, cls, maxcvars ]

	if fmtbits:
		xdigits = ((fmtbits +7) // 8) *2
		res     = ints2xdigits(res, xdigits)

	return res


##--------------------------------------
def hdr2descr(h, lang='C'):
	vars, addl, cls, maxcv = h

	return f'/* {vars}+{addl} vars, {cls} cls, nr.vars<={ maxcv }/cls */'


##--------------------------------------
def ctype(bits):
	bytes = (bits +7) // 8
	return f'uint{ bytes *8 }_t'
## XXX


##--------------------------------------
## empty construct for SAT solver aux. data
##
def satsolv_init0():
	return {
		'delv_units':     {},
		'delv_veh_units': {},
		'vars':           [],
		'added_vars':      0,
		'constraints':    [],
	}


##--------------------------------------
def use_satsolver():
	return True


##--------------------------------------
def satsolv_is_debug(level=1):
	if not ('SATDEBUG' in os.environ):
		return False

	return True


##--------------------------------------
## extract list of variables referenced by template
## pass only numeric variables
##
def clauses2varrefs(cls):
	maxref = -1
	maxref = max(max(maxref, max(abs(v)  for v in c))
	             for c in cls)
	return maxref

## TODO: check that all variables are referenced


##-----------------------------------------
## wrapper for uniform new-variable name construction
##
def satsolv_new_varname(nr=0):
	return f'{ sSAT_2ND_VAR }{ nr +1 }'


##-----------------------------------------
## auto-registers next name with given prefix and solver-derived var.number
##
def sat_new_varname2(sat, prefix=sSAT_2ND_VAR):
	nname = satsolv_nr_of_added_vars(sat) +1
	nname = prefix +str(nname)

	satsolv_register_added_vars(sat, 1)
	satsolv_add_1var(sat, nname)

	return nname


##-----------------------------------------
## return 2x list, of signs ('-' or empty) and of sign-less IDs
## input is list of text IDs, possibly with signs
##
def satsolv_str2ids(ids):
        sgns = list(('-'  if (i[0] == '-')  else '')  for i in ids)
        curr = list(re.sub('^-', '', i)  for i in ids)

        return sgns, curr


##--------------------------------------
## extract raw ID list from clauses; strips any leading '-'
## reduces to unique list, in order of apperance
##
def satsolv_clauses2ids(cls):
	r = []

	for c in cls:
		if isinstance(c, list):
			r.extend(id  for id in c)
			continue

		for id in satsolv_str2ids(c.split())[1]:
			if not id in r:
				r.append(id)

			## str2ids returns (sign, sign2) (id1, id2) etc.
			## pass through only id1/2 etc.

	return r


##--------------------------------------
## remove 'x' from the 'arr' list of integers
## values >x are renumbered to remove x
##
## follows SAT notation, so values are 'pushed towards 0'
##
def ints2renumber(arr, x):
	return [ v  if (abs(v) < x)  else ((v - 1)  if (v > 0)  else (v + 1))
	         for v in arr ]


##--------------------------------------
def clauses_max_varnr(cls):
	maxv = max(max(abs(v)  for v in c)  for c in cls)
	return maxv


##--------------------------------------
## inner core of template_specialize()
## 'val' is True or False; others must have been managed before calling
##
## TODO: restricted to removing 'True' fixed values
##
## returns None if there are no affected clauses
## specialized/shortened clause list otherwise
##
def clauses_specialize(cls, x):
	res, maxv = [], -1

	print(f'## SPECIALIZE({ x })')

				## any of the clauses referencing X or -X?
	xrefs = [ c  for c in cls  if ((x in c) or (-x in c)) ]
	if not xrefs:
		return None

	for c in cls:
		if (x in c) and (-x in c):
			raise ValueError(f"self-contradictory clause ({c})")

		if (-x in c):
			res.append(ints2renumber([ v  for v in c
			                              if (v != -x) ], x))
		elif (x in c):
			continue    ## 'X' is present; entire clause is skipped

		else:
			res.append(ints2renumber(c, x))

		maxv = max(maxv, max(res[-1]))

	print(f'## SPEC.AFTER: MAX(V)=({ maxv })')

	return res


##--------------------------------------
## simplify clause list, if we know that variable 'X' is fixed True/False
## clauses MUST all be numeric (non-symbolic)
##
## updates 't' template in-place, incl. removing/renumbering affected variables
## NOP with val==None, which means 'undefined' in our cases
##
## removes additional-variable count with addl (since most of our
## default-forced variables are additional ones)
##
## recurring pattern: template for expression X(...) is generated;
## X as return value is known. (typical example: 1-of-N, with guarantee
## or global constraint)
##
## simplifies clauses which feature 'X' True:
##    A X   ->          discard clause: 'A' never contributes evaluation
##    B -X  ->  B       -X is never True: 'B' alone controls evaluation
##
def template_specialize(t, x, val=True, addl=True):
	if ((val != True) and (val != None)):
		raise ValueError(f'unsupported fixed var/value ({ val })')
	if val == None:
		return

	res = clauses_specialize(t[ 'clauses' ], x)
##	res = []
##	for c in t[ 'clauses' ]:
##		if (x in c) and (-x in c):
##			raise ValueError(f"self-contradictory clause ({c})")
##
##		if (-x in c):
##			res.append(ints2renumber([ v  for v in c
##			                              if (v != -x) ], x))
##		elif (x in c):
##			pass        ## 'X' is present; entire clause is skipped
##
##		else:
##			res.append(ints2renumber(c, x))

	if res == None:
		return

## TODO: is there a reusable 'normalize' variant?

	t[ 'clauses'    ] = res
	t[ 'nr.clauses' ] = len(res)
	t[ 'add.vars'   ] -= (1  if addl  else 0)

	if t[ 'result' ] == x:
		t[ 'result' ] = 0

	t[ 'outputs' ] = [ v  for v in t[ 'outputs' ]  if (v != x) ]

	return t


##--------------------------------------
## map variables' list to their integer equivalent
## variables may begin with '-', mapped to negated form (idx<0 in solver input)
##
## TODO: simplified to a form which could be list-comprehended
##
## see also:
##
def satsolv_vars2ints(sat, vars):
	res = []

	for v in vars:
		sgn, val = 1, v

		if val[0] == '-':
			sgn = -1
			val = val[1:]

		vidx = sat[ "vars" ].index(val)

		res.append(sgn * (vidx +1))

	return res


##--------------------------------------
## intermediate set: "not in sat['vars']" is slow re-search
##
def satsolv_add_vars(sat, vars):
	if sat:
		seen = set(sat['vars'])
		v = (v  for v in vars  if (not v in seen))
		sat[ 'vars' ].extend(v)


##--------------------------------------
def satsolv_add_1var(sat, var):
	if sat and (not var in sat[ 'vars' ]):
		sat[ 'vars' ].append(var)


##-----------------------------------------
## partition l into (roughly) k-sized parts
##
## in Python v3.12+, this will be itertools.batched()
##
def list2split(l, k):
	return [l[ i*k : (i+1)*k ]
		for i in range((len(l) +k -1) // k)]


##-----------------------------------------
sNALL0 = 'NZ'                     ## suffix for not-all-(values-)zero +variable
sNALL1 = 'ALL1'                   ## suffix for all-(values-)one +variable


##-----------------------------------------
## base, non-negated form of 'var'
def sat_true(var):
	assert(var != 0)
	return abs(var)


##-----------------------------------------
## polymorphic negation
##   - integers: swap sign; 0 is invalid input
##   - strings/symbolic names: add or remove leading '-'
##     - we ensure negation is always canonical, reducing '--' to ''
##
def sat_not(var):
	if isinstance(var, int):
		if var == 0:
			raise ValueError("SAT-negate(0)")

		return -var

			## symbolic name

	if var[:2] == '--':
		raise ValueError("multi-negated symbolic variable")

	return var[:1]  if (var[:1] == '-')  else '-' +var


##-----------------------------------------
## returns clause forcing variable to 'value'
## just a trivial macro to mark context
##
def satsolv_const(var, value=True):
	return f'{ var }'  if value  else f'-{ var }'


##-----------------------------------------
## add fixed-value clause for 'var' if value is True or False
## mark +variable as output if value is not forced
##
## returns updated template to allow chaining
##
def satsolv_1output(templ, var, value=None):
	assert((value == None) or (value == True) or (value == False))

	if value == None:
		templ[ 'nr.outputs' ] += 1
	else:
		templ[ 'clauses' ].append([ var ])
		template_sync(templ)

	return templ


##-----------------------------------------
## add a clause forcing 'var' to 'value' unless already registered
## raises exception if conflicting value was already forced
##
def satsolv_force_const1(sat, var, value=True):
	print(sat[ 'fixed' ])
	assert(0)
	cls.append(satsolv_const(result))


##-----------------------------------------
## pack force etc. logic for 'value' param of satsolv_1output()
##
def sat_1output_value(force, value=True):
	return value  if force  else None


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

	if negate:                     ## X(N)OR only swap truth table polarity
		pol = [ ' ', '-', '-', ' ', ]
	else:
		pol = [ '-', ' ', ' ', '-', ]

	cls.extend([                         ## truth table for "{lf} XOR {rg}"
		f' {var1}  {var2} { pol[0] }{ result }',
		f'-{var1}  {var2} { pol[1] }{ result }',
		f' {var1} -{var2} { pol[2] }{ result }',
		f'-{var1} -{var2} { pol[3] }{ result }',
	])

	negstr = 'NOT '  if negate  else ''

	return cls, result, f'{ result } := { negstr }({var1} XOR {var2})'


##-----------------------------------------
## claues which reject var1 == var2
##
## expect to be used as simplified form for XOR-like applications,
## such as a building block for 1-of-2
##
## all our current uses expect implicit force (which is what allows
## simplified representation)
##
def satsolv_diff1_template(var1, var2, rv=0):
	res = template0('NEQ(2)', inputs=2)

	res[ 'clauses' ] = [             ## truth table for "{var1} != {var2}"
		[ sat_not(var1),         var2,  ],
		[         var1,  sat_not(var2), ],
	]

	return res


##-----------------------------------------
## (var1 XOR var2) truth table
##
def satsolv_xor1_template(var1, var2, rv=0, negate=False, force=False,
                          descr=''):
	if descr == '':
		descr = 'XNOR(2)'  if negate  else 'XOR(2)'

	res  = template0(descr)
	##
	res[ 'add.vars' ] = 1

	if rv == 0:
		rv = -3  if negate  else 3
	else:
		rv = sat_true(rv)

	res[ 'clauses' ] = [             ## truth table for "{var1} XOR {var2}"
		[         var1,          var2,  sat_not(rv), ],
		[ sat_not(var1),         var2,          rv,  ],
		[         var1,  sat_not(var2),         rv,  ],
		[ sat_not(var1), sat_not(var2), sat_not(rv), ],
	]
	template_sync(res)

	return satsolv_1output(res, rv, sat_1output_value(force, not negate))


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
## TODO: merge with AND (or into _and1)
## TODO: simplify (N)AND(..) == True/False paths
##
def satsolv_nand1(var1, var2, result=None, template=False):
	cls  = []

	if result == None:
		result = f'{ var1 }_nn_{ var2 }'

			## placeholders, for column alignment
			## incl. +1 column since aligns with negated column
	v1p = ' ' * (len(var1) +1)
	v2p = ' ' * (len(var2) +1)

	cls.extend([
		f'-{var1} -{var2} -{result}',
		f' {var1} { v2p }  {result}',
		f' {var2} { v1p }  {result}',
	])

	return cls, result, f'{ result } := ({var1} NAND {var2})'


##-----------------------------------------
## raw clauses for two-input OR
##
## returns assigned variable and clauses
## TODO: sync assign-in results, then adapt to that
##
def satsolv_or2(var1, var2, result, negate=False, force=False, template=False):
						## negate: sign for -R/R

## TODO: obsoleted if split properly -> separate ''/- fields
	rsign1, rsign2 = ('', '-')  if negate  else ('-', '')
		## sign(R) in all-enclosing (1) and per-variable (2) lines

	asssert((force == False) or (force == None))

	if template:
## TODO: numeric only; add symbolic form
## TODO: use template0() calls and remove standalone pieces
		return {
			'inputs':   2,
			'add.vars': (0  if force  else 1),
			'clauses': [
				[],
			]
		}


	return result, [
#		[ ' ', var1, ' ', var2, '-', result ],
#		[ '-', var1, ' ', result,           ],
#		[ '-', var1, ' ', result,           ],

		f' {var1} {var2} { rsign1 }{result}',
		f'-{var1} { rsign2 }{result}',
		f'-{var2} { rsign2 }{result}',
	]


##-----------------------------------------
## clause possibly forcing a variable to True/False 'value'
## []  if not forced
##
def clause2set(var, value, force=True):
	if force:
		return [ var  if value  else -var ]
	return []


##-----------------------------------------
## numeric 'vars' implies non-symbolic template generation
## see 'Template representation'
##
## 'rvar' specifies result variable if >0
## does not add >1 additional variable
##
## TODO: merge forced-N/AND templates all here
##
def satsolv_and_template(vars, rvar=0, negate=False, force=False):
	vars = vars2varlist(vars)
	res  = template0('NAND'  if negate  else 'AND', inputs=len(vars))

	rvar = len(vars)+1  if (rvar == 0)  else abs(rvar)          ## force >0

## TODO: polymorphic version, picking max(vars)+1 etc. in
## a type-consistent manner

	if isinstance(vars[0], int):               ## numeric list, 'vars' == N
		val2set = []           ## set to [ variable, value ] if forced

		if len(vars) == 1:
			if force:                ## OR(1) -> force one variable
				res[ 'descr' ] += '(1)->force'
				val2set = [ vars[0], not negate ]

			else:          ## NOP: single variable, arbitrary state
				res[ 'descr' ] += '(1)->NOP'
			res[ 'add.vars' ] = 0

		else:
			res[ 'descr'    ] += f'({ len(vars) })->v{rvar}'
			res[ 'add.vars' ] = 1

				## 1) not(A) | not(B) | R   (A & B) -> R
				## 2) A | not(R)            not(A) -> not(R);...
				## 3) B | not(R)

## TODO: changes w/ symbolic form
			if negate:
				rvar = sat_not(rvar)

## not(A) | not(B)   if R is known True

			res[ 'clauses' ] = [ [ sat_not(v)  for v in vars ] ]

			if force != True:
				res[ 'clauses' ][-1].append(rvar)
				res[ 'clauses' ].extend(
					[ [ v, sat_not(rvar) ]  for v in vars ]
				)
			else:
				res[ 'descr'    ] += '(CONST)'
				res[ 'add.vars' ] -= 1

##				val2set = [ rvar, not negate ]
				pass

## TODO: factor out
		if val2set:
			res[ 'clauses' ].append(
				clause2set(val2set[0], val2set[1], force=force)
			)
		return res

	assert(0)


##-----------------------------------------
## if variable spec is a single integer >0, it implies 1..N
##
def vars2varlist(vars):
	if isinstance(vars, int):                  ## scalar: N (nr. of inputs)
		if vars <= 0:
			raise ValueError('invalid input count')
		return list(range(1, vars+1))

	if not isinstance(vars, list):
		raise ValueError('expected variable-list')

	if isinstance(vars[0], int):               ## scalar: N (nr. of inputs)
		if 0 in vars:
			raise ValueError('input-variable list contains 0')
		return vars

## rest: string list
	return vars


##-----------------------------------------
## numeric 'vars' implies non-symbolic template generation
## see 'Template representation'
##
## 'force'  True/False specify aggregate truth value (only True used)
##
def satsolv_or_template(vars, rvar=0, negate=False, force=None, unitbits=0):
	vars = vars2varlist(vars)
	res  = template0('OR', inputs=len(vars))

	assert(force != False)

	rvar = len(vars)+1  if (rvar == 0)  else abs(rvar)          ## force >0

	if isinstance(vars[0], int):               ## numeric list, 'vars' == N
		val2set = []           ## set to [ variable, value ] if forced

		res[ 'outputs' ] = []  if (force == True) else  [ len(vars) +1 ]  

		if len(vars) == 1:
			if force == True:        ## OR(1) -> force one variable
				res[ 'descr' ] = f'OR.FORCE(1)->force'
				val2set = [ vars[0], not negate ]

			else:          ## NOP: single variable, arbitrary state
				res[ 'descr' ] = f'OR(1)->NOP'

		else:
			op = 'OR'  + ('.FORCE'  if (force == True)  else '')
			res[ 'descr'    ] = f'{ op }({ len(vars) })->v{rvar}'
			res[ 'add.vars' ] = (0  if (force == True)  else 1)

				## 1) A | B | not(R)  not(A) & not(B) -> not(R)
				## 2) not(A) | R      A -> R; B -> R  ...
				## 3) not(B) | R

				## when forced to True:
				## (1) ... | R  clauses dropped (R -> always OK)
				## (2) A | B | ... | N  is the only clause

				## when forced to False: NOR
				## only not(A), not(B) etc. clauses remain

			if negate:
				rvar = sat_not(rvar)

			res[ 'clauses' ] = [ vars[:] ]

## simplifications with forced-True
## A | B | ... -R  skips '-R' since it is always False
## not(A) | R  ->  trivially satisfied with forced 'R'  ->  skip clause

			if force == True:
				pass
##				val2set = [ rvar, not negate ]
			else:
				res[ 'clauses' ][-1].append(sat_not(rvar))
				res[ 'clauses' ].extend(
					[ [ sat_not(v), rvar ]  for v in vars ]
				)

		if val2set:
			res[ 'clauses' ].append(
				clause2set(val2set[0], val2set[1], force=force)
			)

		res[ 'nr.clauses' ] = sat_clauses_count(res[ 'clauses' ])
		return res

	assert(0)


##-----------------------------------------
## numeric templates assume 1..V base variables and V+1..V+A additional ones
##
## shift template for base to start at 'vars' and additional ones
## at extra 'addl_vars'
##
## rebases outputs' indexes with 'result' True
##
## example: +1 +3 will shift 2+1-variable range to:
##    [1, 2], [1, 3] -> [2, 3], [2, 7]
##    - 1 and 2 are in the input-var range, shift by +1
##    - 3 is additional-var range, shift by +1(input)+3(add'l)
##
## NOP, checking only 't' with 'vars' and 'addl_vars' both 0
## TODO: currently, we do not rebase repeatedly
##
def template_rebase(t, vars=0, addl_vars=0, result=True):
	ni, na = t[ 'inputs' ],  t[ 'add.vars' ]
	bi, ba = t[ 'in.base' ], t[ 'add.base' ]

	if min(ni, na) < 0:
		raise ValueError('invalid template-variable count')

	if max(bi, ba) > 0:
		raise ValueError('template already rebased')

## TODO: fix rest
	res = template0(t[ 'descr' ], ni, in_base=bi+vars)
##		'descr':      descr,
##		'outputs':    [],
##		'add.vars':   0,
##		'nr.outputs': 0,             ## if >0, N variables are outputs
##		'result':     0,             ## index if >0; TODO: multi-valued
##		'in.base':    in_base,
##		'add.base':   0,
##		'clauses':    [],
##		'nr.clauses': 0,
	res[ 'add.vars' ] = na
	res[ 'add.base' ] = ba +addl_vars

	rshift = vars  if result  else 0

## TODO: remove; pick up everything from template0()
	res = {
		'descr':    t[ 'descr' ],
		'inputs':   ni,
		'outputs':  list((rshift +r)  for r in t[ 'outputs' ]),
		'add.vars': na,
		'in.base':  bi +vars,
		'add.base': ba +addl_vars,
	}
	cls = []

	for c in t[ 'clauses' ]:
			## any of the combinations shifting out of range?
		oorange = [ i  for i in c  if (abs(i) > bi+ba+ni+na) ]

		if bi+ba:
			oorange.extend(i  for i in c  if (abs(c) < ni+na))

		if oorange != []:
			raise ValueError(f'invalid template-var index ({c})')

		mapped = []
		for v in c:
			shift = vars  if (abs(v) <= ni)  else vars +addl_vars
			mapped.append((v +shift)  if (v > 0)  else (v -shift))
		cls.append(mapped)

	res[ 'clauses' ] = cls
	template_sync(res)

	return res


##-----------------------------------------
## polymorphic: accepts template, or anything with cls['clauses'],
## or direct listing
##
## modifies 'ref'
##
def append_clauses(ref, cls):
	ref.extend(cls[ 'clauses' ])


##-----------------------------------------
## predefined templates for small-N "0/1-of-N" expressions
## 'vids', if not empty, contains IDs for 'vars' (which, otherwise,
## is typically just 1..N, f.ex. when from nested template calls)
##
## see satsolv_1n_few(), which shares logic
##
def satsolv_1ofn_2prod_few_template(vars, allow0=False, force=False,
                                    vids=[]):
	res, r = [], template0(('0/1'  if allow0  else '1') +
	                       f'-of-N({ len(vars) })')
	r[ 'inputs' ] = len(vars)

## TODO: clean up res/r/sub-object assignments
## TODO: does _and_template() etc. already contain small-N templates?

## TODO: allow0/force: redundant; factor out common logic

	if vids == []:
		vids = vars[:]

	if len(vars) == 1:                ## 0/1: anything; 1: var must be True
		r[ 'descr'] += ('->NOP'  if allow0  else  '->force')
		if (not allow0) or force:
			r[ 'clauses' ] = [ [ vars[0] ] ]
			template_sync(r)
		return	r

	elif len(vars) == 2:                        ## 1-of-A/B  or  0/1-of-A/B
		rd =  r[ 'descr' ] + ('->NAND'  if allow0 else  '->NEQ')
		rd += f'[{ vids[0] },{ vids[1] }]'
		if allow0:                     ## reject simultaneous True only
			res = satsolv_and_template(vars, negate=True)
			assert(0)
## TODO: allow0/force: factored-out logic removes assertion
		else:
			res = satsolv_diff1_template(vars[0], vars[1])

		res[ 'descr' ] = rd
		return res

	elif len(vars) <= 5:    ## prohibit simultaneous pairs of variables
				## no pair of variables is simultaneously true
		r[ 'descr' ] += '==NO.PAIRS'
		r[ 'clauses' ] = [
			[ sat_not(v1), sat_not(v2), ]         ## NOT(v1 AND v2)
				for v1, v2  in allpairs(vars)
		]

## TODO: simplified OR: we know that result is True -> simplifies ->
##     > p cnf 4 8
##     > -1 -2 0
##     > -1 -3 0
##     > -2 -3 0       ## part 1: prohibit (1,2) (1,3) or (2,3)
##     > 1 2 3 -4 0    ## OR(1,2,3)
##     > -1 4 0              ## -> trivially satisfied with 4 True
##     > -2 4 0              ## ...
##     > -3 4 0              ## ...
##     > 4 0                 ## -> fixing 4 == OR == True
## simplifies to:
##     > p cnf 3 4
##     > -1 -2 0
##     > -1 -3 0
##     > -2 -3 0       ## part 1: prohibit (1,2) (1,3) or (2,3)
##     > 1 2 3 0       ## ...plus: at least one...

		if not allow0:
#			r[ 'descr' ] += '+OR'
#			r1 = satsolv_or_template(vars, force=force)
#				##
#			r[ 'add.vars' ] += r1[ 'add.vars' ]
#			r[ 'clauses'  ].extend(r1[ 'clauses' ])
				## inputs are shared: no clause/index to rebase
			r[ 'descr' ] += '+AT.LEAST.1'
			r[ 'clauses'  ].append([ v  for v in vars ])

		template_sync(r)
		r[ 'nr.outputs' ] = 0  if force  else 1

		return r

	return None

	return res


##-----------------------------------------
## 1-of-N decomposition, example for 12 inputs (1..12):
##
##   1) not a trivial example, such as 1-of-2 == XOR
##      - see satsolv_1ofn_2prod_few_template() for recognized cases
##
##   2) pick PxQ = 3x4 as 2D matrix dimensions; original inputs
##      set axes. as a convention, we assign P and Q variables, in
##      this order; each OR a row/column of the inputs' matrix:
##
##        Q[4]  [16]  [ 1,  2,  3]
##              [17]  [ 4,  5,  6]
##              [18]  [ 7,  8,  9]
##              [19]  [10, 11    ]
##                    [13, 14, 15]  P[3]
##
##        ->    1 -> 16, 13         ## all pairs, so no real OR is needed
##              2 -> 16, 14
##              3 -> 16, 15
##              4 -> 17, 13
##                ..
##             10 -> 19, 13
##             11 -> 19, 14
##
##        -> 13 = OR(1, 4, 7, 10)   ## 1st index: nr. of inputs +1
##           14 = OR(2, 5, 8, 11)
##           15 = OR(3, 6, 9, 12)
##        -> 16 = OR(1, 2, 3)       ## 1st index: nr. of inputs +1 +nr(P axis)
##           17 = OR(4, 5, 6)
##           ...
##          -> map PxQ 2D matrix into per-row ORs: not more than one
##             P/Q axis variable may be set for any of the 2D matrix vars:
##             [-16, 1], [-13, 1],
##             [-16, 2], [-14, 2],
##             [-16, 3], [-15, 3],
##             [-17, 4], [-13, 4],
##             [-17, 5], [-14, 5],
##             [-17, 6], [-15, 6],
##             [-18, 7], [-13, 7],
##             [-18, 8], [-14, 8],
##             [-18, 9], [-15, 9], [-19, 10], [-13, 10],
##	[-19, 11], [-14, 11], [-19, 12], [-15, 12]],
## XXX
##
##        -> solver descends into 1-of-3(P) and 1-of-4(Q):
##           -> 13 OR 14 OR 15 -> 20; 20 is always set to ensure 1-of-3(P)
##              [-13, -14]         ## NOT(13 AND 14)
##              [-13, -15]         ## NOT(13 and 15)
##              [-14, -15]         ## NOT(14 and 15)
##              [13, 14, 15, -20]  ## any(13, 14, 15) -> 20
##              [20]               ## 20 is True: 1-of-3
##                                 ## +1 additional variable over P axis vars
##              - note: 13..15 already assigned as P[] variables
##                - 20 is first aux. variable after P[] and Q[] one
##              - aux. variables of P[] will appear after P[] and Q[] vars
##
##           -> 16 OR 17 OR 18 OR 19 -> 21
##              [-16, -17]             ## NOT(16 AND 17)
##              [-16, -18]             ## NOT(16 AND 18)
##              [-16, -19]             ## NOT(16 AND 19)
##              [-17, -18]             ## NOT(17 AND 18)
##              [-17, -19]             ## NOT(17 AND 19)
##              [-18, -19]             ## NOT(18 AND 19)
##              [16, 17, 18, 19, -21]  ## any(17..19) -> 21
##              [21]                   ## 21 is True: 1-of-4



##-----------------------------------------
## 0/1-of-N template
##
## see satsolv_1ofn_2prod(): shares much of the same logic
##
@cache
def satsolv_1ofn_2prod_template(vars, varbase=0, addbase=0, allow0=False,
                                force=False):
	rstr = ('0/1'  if allow0  else '1') + '-of-N'
	vars = vars2varlist(vars)
	r    = template0(f'{ rstr }({ len(vars) })', inputs = len(vars))

	if isinstance(vars[0], int):                            ## numeric list
		few = satsolv_1ofn_2prod_few_template(vars, allow0=allow0,
		                                      force=force)
		if few:
			return few

		ivcount = len(vars)    ## input-var-count; recurring expression
		result  = 0

		p, q = matrix2pq(vars)

##		if not force:           ## if 1-of-N is not forced, report
##		                        ## as a standalone variable
##		r[ 'add.vars' ] += 1
##		result = ivcount +1
##		ivcount += 1

					## adds P+Q axis variables, here
					## w/o any subsequent expressions' vars
		r[ 'add.vars' ] += p +q
					## P+Q axis vars appended immediately
					## after inputs, in this order
		pvar = list(range(ivcount +1,    ivcount +p +1   ))
		qvar = list(range(ivcount +p +1, ivcount +p +1 +q))
## TODO: proper non/response split -> offset constant

		comm =  f'{ rstr }(v1..v{ ivcount }->'
		comm += f'{ p }[a{ pvar[0] }..a{ pvar[-1] }]x'
		comm += f'{ q }[a{ qvar[0] }..a{ qvar[-1] })'

					## one var each for P*Q matrix
					## elements
		xyvars = [ vars[ i*p : (i+1)*p ]  for i in range(q) ]
					## last row may contain less
					## variables, if N < P*Q
					##
					## these are not new vars,
					## just a grouping of inputs:
					##   12 -> [4][3] ->
					##     [[1, 2, 3], [4, 5, 6],
					##      [7, 8, 9], [10, 11, 12]]

		assert(not allow0)
## TODO: check if force/allow0 preconditions hold below; then remove

		pt = satsolv_1ofn_2prod_template(p, force=True)
		qt = satsolv_1ofn_2prod_template(q, force=True)

		ptv = clauses2varrefs(pt[ 'clauses' ])
		qtv = clauses2varrefs(qt[ 'clauses' ])

		comm += f',({ pt[ "descr" ] })'
		comm += f'x({ qt[ "descr" ] })'

## TODO: force base0 variable assignment; then we do not need
## to subsequently rebase
## TODO: merged in_base=...; use that without need to rebase

				## ...original inputs... || vars(P) || vars(Q)
				## plus additional variables from P
				##
				## axis vars(P) start after original inputs
				## additional variables XXX
		pt = template_rebase(pt, ivcount,    q)
		qt = template_rebase(qt, ivcount +p, pt[ 'add.vars' ])

		r[ 'add.vars' ] += pt[ 'add.vars' ] + qt[ 'add.vars' ]
		r[ 'clauses'  ].extend(pt[ 'clauses' ])
		r[ 'clauses'  ].extend(qt[ 'clauses' ])

		maxvar = clauses2varrefs(r[ 'clauses' ])

		print(f'## MAX(VARS)={ maxvar }')

		if (maxvar != r[ 'add.vars' ] + r[ 'inputs' ]):
			print('## ERROR: MAX(VAR) MISMATCH ', maxvar,
				r[ 'add.vars' ] + r[ 'inputs' ],
				r)
			sys.stdout.flush()
			raise ValueError("variable-count mismatch")

				## at-most-1(vars): each 'var' corresponds to
				## not more than one pvar/qvar ->
				##  (NOT(v) OR p(column)) AND (NOT(v) OR q(row))
				##
				## note: pvar[] and qvar[] are column+row
				## variables, respectively

		for qi, qr in enumerate(xyvars):          ## loop(q), row
			for pi, var in enumerate(qr):     ## loop(p), variable
				r[ 'clauses' ].extend([
					[ sat_not(var), qvar[ qi ] ],
					[ sat_not(var), pvar[ pi ] ],
##
## note: transposed representation
##					[ sat_not(qvar[ qi ] +1), var, ],
##					[ sat_not(pvar[ pi ] +1), var, ],
				])

		r[ 'comments'   ] = comm
		r[ 'nr.outputs' ] = 0  if force  else 1

## TODO: enforce only at top level even with 'force', or just return
## the index as usual, and let top-level caller set to True

#		if force:
#			r[ 'clauses' ].append([ result ])
## TODO: merge (1) into known cases (2) general True/False lookups

		template_sync(r)

		return r

## TODO: symbolic mapping
	assert(0)


##-----------------------------------------
def satsolv_sum_few(vars, emax, elems):
	if elems == 1:
		return None

	if emax == 1:
		if elems == 1:                        ## SUM(1-bit A) == bit(A)
			return None
		if elems == 2:
			return None

	return None


##-----------------------------------------
## 'vars' is either list of bits, or nr. of variables
## 'emax' specifies max. value to represent; 0 if full range
##
@cache
def satsolv_sum_template(vars, emax):
##	RRR
	if len(vars) < 1:
		raise ValueError("SUM: invalid max(elems)")

	r = satsolv_sum_few(vars, emax, elems)
	if r:
		return r

	r = template0(f'SUM({ elems } x (0..{ emax }))')

	return r


##-----------------------------------------
## sample: A; B; ...; R = A | B | ...
##     1) A | B | not(R)      not(A) & not(B) -> not(R)
##     2) not(A) | R          A -> R; B -> R  ...
##     3) not(B) | R
##        ...
##
## NOR with 'negate' (negates R in all clauses)
## 'force' True degenerates into 'A | B ...' (all the not(...)|R clauses
## are trivially satisfied)
##
## returns list of clauses + control variable + comment
##
## TODO: organized propagation of +- signs (in-band)
## TODO: manage 'force'
##
def satsolv_or(base, vars, result=None, negate=False, force=False,
               template=False):

	if template:
		return satsolv_or_template(vars, negate=negate, force=force)
	cls = []
	v   = sorted(vars)
	all = list((base +b)  for b in  v)

	if result == None:
		result = base + sNALL0

## see also: satsolv_or2()
	rsign1, rsign2 = ('', '-')  if negate  else ('-', '')
		## sign(R) in all-enclosing (1) and per-variable (2...) lines

	if not force:
		all.append(f"{ rsign1 }{ result }")

	cls.append( " ".join(all) )                   ## A | B | not(N)

	terms = list((base +b)  for b in v)

	if not force:
		cls.extend((f'-{ t } { rsign2 }{ result }')  for t in terms)
					## not(...) | R  clauses, if applicable

	if negate:
		req = f'NOR(' +(",".join(terms)) +')'
	else:
		req = f'(' +(" OR ".join(terms)) +')'

	return cls, result, f'{ result } := { req }'


##-----------------------------------------
## sample: A; B; N = A & B
##     1) not(A) | not(B) | N        (A & B) -> N
##     2) A | not(N)                  not(A) -> not(N); not(B) -> not(N)
##     3) B | not(N)
##
## None 'result' auto-assigns variable name
## 'negate' inverts to NAND (by swapping N sign)
##
## returns list of clauses + comment
##
## manages AND-of-one variable (just passes through or turns to NOT)
##
def satsolv_and(base, vars, result=None, force=False, negate=False,
                template=False):
	if template:
		return satsolv_and_template(vars, negate=negate, force=force)

	cls = []
	v   = sorted(vars)

	if len(vars) == 1:
		return vars[0], vars[0], f'AND({ vars[0] }) == { vars[0] }'

	rsign1, rsign2 = ('', '-')  if negate  else ('-', '')

	if result == None:
		result = base + sNALL1

	all = list((f"-{ (base +b) }")  for b in  v)
	all.append(f"{ rsign1 }{ result }")
		##
	cls.append( " ".join(all) )                   ## not(A) | not(B) | N

	terms = list((base +b)  for b in v)

	cls.extend((f'{ t } { rsign2 }{ result }')  for t in terms)

	return cls, result, f'{ result } := (' +(" AND ".join(terms)) +')'


##-----------------------------------------
## comment for 1-of-N to ...result... SAT clause/s
## 'vars' is list of input variables
##
## TODO: where do we special-case N=1, things like that?
##
def sat_1ofn_comment(res, vars):
	vlist = ",".join(vars)

	return f'1-of-N[={ len(vars) }]: ({ res }) for ({ vlist })'


##-----------------------------------------
## hardwired 0/1-of-N for small N with trivial expressions
##
## returns None if not handled
##         [ top-level variable, [ newly added variables, ], clauses, comment ]
##             if solution is applicable
##
def satsolv_1n_few(sat, vars, nr=0, allow0=False, result=None, force=False):
	if len(vars) == 1:
		if allow0:                                ## A=0/1 -> no clause
			return [ [], [], [], '', ]
		else:
				## explicit clause forcing var to True
				## do not bother trimming replicated clauses
				##
			cls = [ vars[0] ]  if force  else []

			return [ vars[0], [], cls, '', ]      ## 1-of-N(A) == A


	##------------------------------
	if len(vars) == 2:                          ## 1-of-A/B  or  0/1-of-A/B
		if allow0:                     ## reject simultaneous True only
			if result == None:
				result = sat_new_varname2(sat, 'NAND')

			cls = [ f'-{ vars[0] } -{ vars[1] }', ]
			cmt = f'at-most-1({result})=>NAND({vars[0]},{vars[1]})'
			return [ [], [], cls, cmt, ]
						## only clause, no new variable
## TODO: merge return paths
		if result == None:
			result = sat_new_varname2(sat, 'N1xXOR')

		cls, _, _ = satsolv_xor1(vars[0], vars[1], result=result)
		cmt = f'at-most-1({result}) => ({vars[0]} XOR {vars[1]})'

		if force:
			satsolv_force_const(sat, result)
			cls.append(satsolv_const(result))        ## XOR is true

		return [ result, [ result, ], cls, cmt, ]


	##------------------------------
	if len(vars) == 3:
## TODO: use a more compact encoding than OR+not-pairs
				## no pair of variables is simultaneously true
		cls = [ f'-{v1} -{v2}'  for v1, v2  in allpairs(vars) ]
		or3 = []
## TODO: proper signs and indexing

		if not allow0:
			result = sat_new_varname2(sat,'THREE2ONEx')
			cls0, or3, _ = satsolv_or('', vars, result)

			cls.extend(cls0)
##			cls.append(satsolv_const(result))
##							## at least one is true

			or3 = [ or3, ]

		return [ result, or3, cls, '', ]

	return None


##-----------------------------------------
## template-generating equivalent of satsolv_1n_few()
## returns None if special case is not recognized
##
## 'vars' is inputs' list, all-numeric or symbolic
##
def satsolv_1n_few_template(vars, allow0=False, force=False):
	if len(vars) == 1:
		if allow0:                                ## A=0/1 -> no clause
			return [ [], [], [], '', ]
		else:
				## explicit clause forcing var to True
				## do not bother trimming replicated clauses
				##
			cls = [ vars[0] ]  if force  else []

			return [ vars[0], [], cls, '', ]      ## 1-of-N(A) == A

	return None


##-----------------------------------------
## Return '(top-level) commander variable', newly added (commander) variables,
## related additional clauses, and comments documenting the collection.
##
## The first element of the commander-variable array is true if and only
## exactly one of 'vars' (variable-name) inputs is True.
##
## commander variables are named 'CMDR...'; prefix MUST NOT be used by others
## TODO: current form restricted to a binary tree
##       may specialize if truth table generator for k>2 fanout is available
##
## 'nr' is the number of defined additional variables, incl. current inputs
## (used in assigning IDs to intermediate ones)
##
## see
##   Kliebert, Kwon: Efficient CNF encoding for selecting 1 of N objects,
##   www.cs.cmu.edu/~wklieber/papers/
##       2007_efficient-cnf-encoding-for-selecting-1.pdf
##   [accessed 2023-02-24]
##
def satsolv_1n(sat, vars, nr=0, allow0=False, result=None):
	if vars == []:
		raise ValueError("called with empty variable list")

	r = satsolv_1n_few(sat, vars, nr=nr, allow0=allow0, result=result)
	if r:
		return r[0], r[1], r[2], r[3]

	##--------------------------------------------------------------------
## TODO: should be factored out, since other expressions may reuse
##       hierarchical grouping+var.assignment

			## recurse: build bottom-up grouping
			## 1st level: groups of original inputs
			## 2nd level: commander variables of 1st level groups...
			## TODO: fixed to fanout of 2
			##
			## TODO: predefine patterns for 3 or 4, and use those
			##
	grps  = list2split(vars, 2)
	grps0 = grps[:]    ## originals; allow modification of grps[]

	assign, newvar = [], []
			## assign[] collects [ ...group..., [ cmd.var ] ] list,
			## in assignment (bottom up) order
			## associating variables with their command variables
	cls = []

	while grps:
		curr, grp0size = [], len(grps)
			## grp0size: initial nr. of pairs at this level

		for g in grps:
			if len(g) == 1:
				assign.append([ [], g[0] ])
				curr.append( g[0] )
				continue
					##
					## if variable is alone in its group,
					## propagate it directly up.
					## in this case, the
					## originating group remains empty
					## and we only
					## store  [ [], [ ...variable... ] ]
					## to assign

				## last assignment: MAY go to 'result'
				##
			if (grp0size == 1) and result:
				nv = result
			else:
				nv = sat_new_varname2(sat)

			assign.append([ g, nv, ])
			curr.append(nv)
				##
			satsolv_add_comment(sat,
				f'  1-of-N command {",".join(g)} -> {nv} ')

		if len(curr) == 1:
			break
		grps = list2split(curr, 2)   ## advance to next level

	if result:
		assign[-1][-1] = result      ## caller-supplied top var.name
		if newvar != []:
			newvar.pop(-1)       ## was last new-var appended, undo

	else:
		result = assign[-1][-1]

					## commander conditions, see section 2
					##
					## these conditions essentially simplify
					## to NAND/OR primitives' clauses,
					## for fanout k=2
	cls = []
	for a in assign:
		c, sub = a[-1], a[-2]
		assert(len(sub) <= 2)   ## in case increasing fanout, but
		                        ## forgetting to update something...
		if sub == []:           ## non-hierarchical, pass-through var
			continue

		_, c2 = satsolv_or2(sub[-2], sub[-1], c)
		cls.extend(c2)
					## commander=OR(...variables...)

					## both sub-variables may not be True
		cls.append( f'-{sub[-2]} -{sub[-1]}' )

	return result, newvar, cls, sat_1ofn_comment(result, vars)


##--------------------------------------
## not checking for replication
##
def satsolv_add_constraint(sat, vars, comment=''):
	if sat and ('constraints' in sat):
		sat[ 'constraints' ].append([ " ".join(vars), comment ])


##--------------------------------------
## register 'raw', preformatted constraint
## not checking for replication
##
def satsolv_add_constraint1(sat, rawc, comment=''):
	if sat:
		sat[ 'constraints' ].append([ rawc, comment ])


##--------------------------------------
def satsolv_add_comment(sat, comment):
	if sat and ('constraints' in sat):
		sat[ 'constraints' ].append([ '', comment ])


##-----------------------------------------------------------
## add clauses for 1-of-N selections over 'vars'
## returns top-level 'command' variable which is True if and only if 1-of-N
##
## append comments and clauses to respective lists
##
def satsolv_1ofn(sat, vars, result=None):
	top, nvars, cls, cmt = satsolv_1n(sat, vars, sat[ 'added_vars' ],
	                                  result=result)

	satsolv_add_vars(sat, nvars)

	sat[ 'added_vars' ] += len(nvars)

	descr = sat_1ofn_comment(top, vars)

	for c in cls:
		satsolv_add_constraint1(sat, sSAT_SYM_PREFIX + c, descr)
		descr = ''

	if satsolv_is_debug():
		for c in cls:
			satsolv_add_constraint1(sat, '', '  ORIG=' +c)

						## force 1-of-N by ensuring
						## commander var is True
	satsolv_add_constraint1(sat, sSAT_SYM_PREFIX + top, descr)

	return top


##-----------------------------------------
## predefined P+Q matrix sizes, in case we know relative costs etc.
##
tMATRIX2PQ = {
	5: [ 2, 3, ],
	6: [ 2, 3, ],

	7: [ 2, 4, ],       ## less levels than 3x3 decomposition?
	8: [ 3, 3, ],       ## less levels than 3x3 decomposition?
	9: [ 3, 3, ],
}


##-----------------------------------------
## 1-of-N or 0-of-N, hierarchical decomposition: pick P+Q matrix sizes
## returns p, q per-axis sizes
##
## TODO: skip N-times-M plus 1 (21 -> 5x5 -> 4x5 +1)
##
def matrix2pq(vars):
			## assume ~square P*Q is optimal
			## TODO: minimize (cost(P) + cost(Q)) -> select P, Q
			##
	if len(vars) in tMATRIX2PQ:
		return tMATRIX2PQ[ len(vars) ]

			## the simplest recommendation is p = floor(sqrt()) -> 
			## q = ceil(n / p)
			##
			## special-case some known-good cases

	p = math.ceil( math.sqrt(len(vars))  )
	if (p ** 2 == len(vars)):
		q = p

	elif (p * (p+1) >= len(vars)):
		q = p + 1

	elif ((p + 1) ** 2 >= len(vars)):
		p, q = p + 1, p + 1

	elif ((p + 1) * (p + 2) >= len(vars)):
		p, q = p + 1, p + 2

	else:
		assert(0)  ## ...optimal selection would eliminate selection...

	return p, q


##-----------------------------------------
## 1-of-N or 0-of-N (selected by 'allow0')
##
## returns [ control variable, [ new/intermediate variables],
##           [ new clauses ], comment ]  tuple
##
## 'force' adds explicit clause ensuring 'result' is True
##
## 'two-product encoding of 0/1-of-N'
##   1) construct P*Q matrix with P*Q >= N
##   2) variables 1..N <-> entries in matrix
##   3) 1-of-N: ensure 1-of-P (X) and 1-of-Q (Y)
##     3.1) selected entry is intersection
##   4) 0-of-N: allow NOR(P) AND NOR(Q) (==NOT(P OR Q)) as well
##   5) only N product variables are used if N<P*Q
##
## note: hierarchical decomposition of 1-of-P/Q
## TODO: use template for small P/Q which we expect to encounter
##
## see:
## Chen: A new SAT encoding of the at-most-one constraint
##   2010-07
##   www.it.uu.se/research/group/astra/ModRef10/papers/
##       Jingchao%20Chen.%20A%20New%20SAT%20Encoding%20of%20the
##       %20At-Most-One%20Constraint%20-%20ModRef%202010.pdf
##
def satsolv_1ofn_2prod(sat, vars, result=None, force=False, allow0=False,
                       template=False):
	if template:
		return satsolv_1ofn_2prod_template(vars, allow0=allow0,
		                                   force=force)

## sat next vars -> nr
	nr, comm, expr = 0, '', []

## TODO: trim added-vs-original variables properly

				## before-after: new/intermediate variables
	nvars_orig = satsolv_nr_of_added_vars(sat)

	expr = f'1-OF-[{ len(vars) }]({ ",".join(vars) })'

## see also: satsolv_1ofn_2prod_template()

	r = satsolv_1n_few(sat, vars, nr=nr, allow0=allow0, result=result)
	if r:
		return r[0], r[1], r[2], r[3]

	p, q = matrix2pq(vars)

	if result == None:
		result = sat_new_varname2(sat,
		                 prefix='N01:' if allow0 else 'N1x')

	comm = f'{ 0  if allow0  else 1 }-of-{ len(vars) } <-> {p}*{q}'
	cls, nvars = [], []

			## 'frame' variables, rows (Q) and columns (P)
			##
	pvars = [ sat_new_varname2(sat, prefix=f'XY{ len(vars) }C')
	                              for i in range(p) ]
			##
	qvars = [ sat_new_varname2(sat, prefix=f'XY{ len(vars) }R')
	                              for i in range(q) ]

					## group inputs as p-times-q product
					##
	xyvars = [vars[ i*p : (i+1)*p ]  for i in range(q)]
					##
					## last row may contain less
					## variables (if N < P*Q)

	if True:
		print(f'## P=1-of-{p} x Q=1-of-{q}')
		print(f'## VARS(P)[{ len(pvars) }]={ pvars }')
		print(f'## VARS(Q)[{ len(qvars) }]={ qvars }')

	pv, pnvars, pcls, _ = satsolv_1ofn_2prod(sat, pvars, allow0=allow0)
	qv, qnvars, qcls, _ = satsolv_1ofn_2prod(sat, qvars, allow0=allow0)

	print(f'## VAR.P={ pv } [{ len(pcls) }] ', pcls)
	print(f'## VAR.Q={ qv } [{ len(qcls) }] ', qcls)

	cls.extend(pcls)
	cls.extend(qcls)
	nvars.extend(pnvars)
	nvars.extend(qnvars)
	print("## NEW.VARS XXX", len(nvars), nvars)

				## both MUST be true for 1-by-1 intersection
				##
	pq_clauses, _, _ = satsolv_and('', [ pv, qv, ], result=result)
	cls.extend(pq_clauses)

				## at-most-1(vars): each 'var' corresponds to
				## not more than one pvar/qvar ->
				##     (NOT(v) OR p) AND (NOT(v) OR q)
				##
	for ri, row in enumerate(xyvars):                  ## loop(q), row
		for ci, col in enumerate(row):             ## loop(p), column
			cls.append(f'-{ col } { pvars[ci] }')
			cls.append(f'-{ col } { qvars[ri] }')
## TODO: sync row+column expressions and notation

	nvars_after = satsolv_nr_of_added_vars(sat)

	if force:
		cls.append(f'{ result }')   ## 0/1-of-N must hold at this level

	print(f'## ADDED.VARS=+{ satsolv_nr_of_added_vars(sat) - nvars_orig }')
		##
	if nvars_after > nvars_orig:
		vlist = ", ".join(sat["vars"][ nvars_orig:nvars_after ])
		print(f'## ADDED.VARS=[{ vlist }]')

	return result, [], cls, comm


##-----------------------------------------
def satsolv_nr_of_added_vars(sat):
	return sat[ 'added_vars' ]  if (sat and ('added_vars' in sat))  else 0


##-----------------------------------------
## increase the number of solver-allocated, intermediate variables
##
def satsolv_register_added_vars(sat, n):
        sat[ 'added_vars' ] += n


##-----------------------------------------
## centralized NOT, to save on recurring logs
##
## just a macro to document NOT-X invocations
## does not need extra variables, just an inverting clause
##
def satsolv_not(sat, var):
	rv = f'-{var}'

	return rv, rv, f'NOT({ var })'


##-----------------------------------------
## NAND, for arbitrary nr of bits
##
## sample: A; B; C; D; N = not(A & B & C & D)
##     1) not(A) | not(B) | not(N)
##     2)      A | N
##     3)      B | N
##     4)      ...
##
## None 'result' auto-assigns variable name
## returns list of clauses, result variable, comment
##
def satsolv_nand_n(sat, vars, result=None):
	cls  = []

	if len(vars) == 1:
		return satsolv_not(sat, vars[0])

	if result == None:
		result = satsolv_new_varname(satsolv_nr_of_added_vars(sat) +1)

	vall = list(f'-{v}'  for v in vars)

	cls.append([ ' '.join(vall) + f' -{result}' ])
	cls.extend([ f' {v} {result}' ]  for v in vars  )        ## 1x each bit

	return cls, result, f'{ result } := NAND({ ",".join(vars) })'


##----------------------------------------------------------------------------
## collapse list to runs of identical entries
##     [ 1, 0, 1, 1 ]  ->  [ [1], [0], [1, 1] ]
##
def arr2runs(arr):
	runs = []

	for v in arr:
		if (runs == []) or (runs[-1][-1] != v):
			runs.append([])
		runs[-1].append(v)

	return runs


##----------------------------------------------------------------------------
## multi-region comparisons, with AND-OR-AND-... alternating regions
## of (multi-bit)V < ...constant... comparisons
##
## 'n' is the number of regions to compare; rules:
##   - not-OR of any bits higher than the most significant 1 (MS AND run)
##        V < 0011xxxx -> (11000000 & V) MUST NOT be >0
##   - AND, if not yet decided and False, means V<...const...:
##            1111..11 000..00 ...
##        V = 0xxxxxxx yyyyyyy ...   ->  V<...const... regardless of x/y
##   - OR, if not yet decided and False, means V>=...const...
##   - trailing OR is irrelevant: can never decide
##     - bits of V in OR region can never be <0
##   - comparisons are quite regular; see expanded examples below:
##     !AND1 | (!OR2 & !AND3)                                generalizes to
##     !AND1 | (!OR2 &  AND3) | ... | (OR<2k> & !AND<2k+1>)
##     use '!AND1' and '-AND1' interchangeably
##
## the descriptions below skip the 'not-OR of any bits higher than the
## constant' term, which will always be implied.
##
## 1 region,  V < 1111..11
##                ==AND1==
## 2 regions, V < 1111..11  000..00
##                ==AND1==  ==OR2==
##     R1/R2 = -AND1
##     as discussed, trailing OR2 can not change result, can be dropped
##   CNF: does not add clause: use constructed AND+invert, or NAND directly
##
## 3 regions, V < 1111..11  000..00  11...1
##                ==AND1==  ==OR2==  =AND3=
##
##     truth table/Karnaugh map, with <AND1 | OR2 | AND3> . <result>
##                       _____AND3
##                000.1  001.1
##                010.1  011.1 |
##              | 110.0  111.0 |OR2
##          AND1| 100.1  101.0
##     R3 = -AND1 | (-OR2 & -AND3)    <=>    -AND1 | (AND1 & -OR2 & -AND3)
##     ----
##     000.1
##     001.1
##     010.1
##     011.1
##     100.1
##     101.0
##     110.0
##     111.0
##  -> CNF equivalent:
##     A) AND1 R3 0             --  -AND1         ->  R3
##     B) OR2 AND3 R3 0         --  -OR2 & -AND3  ->  R3
##     C) -AND1 ANDx -R3 0      -- R3  ->  (-AND1 | ANDx)
##     --- ANDx = (-OR2 & -AND3), from library/function
##
## 4 regions, V < 1111..11  000..00  11...1  000..00
##                ==AND1==  ==OR2==  =AND3=  ==OR4==
##   -> see 3 regions: OR4 can not influence result
##   full truth table/Karnaugh map, with <AND1 | OR2 | AND3 | OR4> . <result>:
##                      _____OR4_____
##              0000.1  0001.1 0011.1  0010.1
##              0100.1  0101.1 0111.1  0110.1 |
##            | 1100.0  1101.0 1111.0  1110.0 | OR2
##       AND1 | 1000.1  1001.1 1011.0  1010.0
##                             -----AND3-----
##
## 5 regions, V < 1111..11  000..00  11...1  000..00  11...1
##                ==AND1==  ==OR2==  =AND3=  ==OR4==  =AND5=
##
##     2) R5 = -AND1 | (-OR2 & -AND3) | (-OR2 & AND3 & -OR3 & -AND4)
##             ==A==   =======B======   ==============C=============
##     -------
##     00000.1   AB
##     00001.1   AB
##     00010.1   AB
##     00011.1   AB
##     00100.1   A C
##     00101.1   A
##     00110.1   A
##     00111.1   A
##     01000.1   A
##     01001.1   A
##     01010.1   A
##     01011.1   A
##     01100.1   A
##     01101.1   A
##     01110.1   A
##     01111.1   A
##     10000.1    B
##     10001.1    B
##     10010.1    B
##     10011.1    B
##     10100.1     C
##     10101.0
##     10110.0
##     10111.0
##     11000.0
##     11001.0
##     11010.0
##     11011.0
##     11100.0
##     11101.0
##     11110.0
##     11111.0
##
##     2) R5 = -AND1 | (-OR2 & -AND3) | (-OR2 & AND3 & -OR3 & -AND4)
##             ==A==   =======B======   ==============C=============
##
##  -> CNF equivalent, 5+1 variables:
##     A) AND1 R5 0                  --  -AND1                        ->  R5
##     B) OR2 AND3 R5 0              --  -OR2 & -AND3                 ->  R5
##     C) OR2 -AND3 OR3 AND4 R5 0    --  -OR2 &  AND3 & -OR3 & -AND4  ->  R5
##     D) -AND1 ANDx ANDy -R5 0      --  R5  ->  (-AND1 | ANDx | ANDy)
##     --- ANDx = (-OR2 & -AND3)
##     --- ANDy = (-OR2 &  AND3 & -OR3 & -AND4), from library/function
##
## 6 regions, V < 1111..11  000..00  11...1  000..00  11...1  000..00
##                ==AND1==  ==OR2==  =AND3=  ==OR4==  =AND5=  ==OR6==
##   -> see 5 regions; OR6 can not influence result
##
## 7 regions, V < 11..11  00..0  11...1  00..0  11...1  00..0  11...1
##                =AND1=  =OR2=  =AND3=  =OR4=  =AND5=  =OR6=  =AND7=
##
##     2) R7 = -AND1 | (-OR2 & -AND3) | (-OR2 & AND3 & -OR4 & -AND5) |
##             (-OR2 & AND3 & -OR4 & AND5 & -OR6 & -AND7)
##
##  -> CNF equivalent, 7+1 variables:
##     A) AND1 R7 0                   --  -AND1                        ->  R7
##     B) OR2  AND3 R7 0              --  -OR2 & -AND3                 ->  R7
##     C) OR2 -AND3 OR3  AND4 R7 0    --  -OR2 &  AND3 & -OR3 & -AND4  ->  R7
##     D) OR2 -AND3 OR3 -AND4 OR5 AND6 R5 0
##                                    --  -OR2 &  AND3 & -OR3 &  AND4 &
##                                        -OR5 &  AND7                 ->  R7
##     E) -AND1 ANDx ANDy ANDz -R7 0  --  R7  ->  (-AND1 | ANDx | ANDy | ANDz)
##     --- ANDx = (-OR2 & -AND3)
##     --- ANDy = (-OR2 &  AND3 & -OR4 & -AND5)
##     --- ANDz = (-OR2 &  AND3 & -OR4 &  AND5 & -OR6 & -AND7)
##
## 8 regions:
##   -> see 7 regions; OR8 can not influence result


## while generating comparisons is straightforward, we just tabulate the
## first few entries. entries indexed by number of runs (so 1111'111 is
## under 1, 111100111 under 3 (as 1111-00-111) etc.
##
## map 2k runs to 2k+1, since a trailing OR term never decides v<..const..
##
tCMP_TRUTHTABLES = [           ## indexed by N-1
	[ ],
]

## N=3
##     A) AND1 R3 0             --  -AND1         ->  R3
##     B) OR2 AND3 R3 0         --  -OR2 & -AND3  ->  R3
##     C) -AND1 ANDx -R3 0      -- R3  ->  (-AND1 | ANDx)
##     --- ANDx = (-OR2 & -AND3), from library/function

## N=5
##     A) AND1 R5 0                  --  -AND1                        ->  R5
##     B) OR2 AND3 R5 0              --  -OR2 & -AND3                 ->  R5
##     C) OR2 -AND3 OR3 AND4 R5 0    --  -OR2 &  AND3 & -OR3 & -AND4  ->  R5
##     D) -AND1 ANDx ANDy -R5 0      --  R5  ->  (-AND1 | ANDx | ANDy)
##     --- ANDx = (-OR2 & -AND3)
##     --- ANDy = (-OR2 &  AND3 & -OR3 & -AND4), from library/function

## N=7
##     A) AND1 R7 0                   --  -AND1                        ->  R7
##     B) OR2  AND3 R7 0              --  -OR2 & -AND3                 ->  R7
##     C) OR2 -AND3 OR3  AND4 R7 0    --  -OR2 &  AND3 & -OR3 & -AND4  ->  R7
##     D) OR2 -AND3 OR3 -AND4 OR5 AND6 R5 0
##                                    --  -OR2 &  AND3 & -OR3 &  AND4 &
##                                        -OR5 &  AND7                 ->  R7
##     E) -AND1 ANDx ANDy ANDz -R7 0  --  R7  ->  (-AND1 | ANDx | ANDy | ANDz)
##     --- ANDx = (-OR2 & -AND3)
##     --- ANDy = (-OR2 &  AND3 & -OR4 & -AND5)
##     --- ANDz = (-OR2 &  AND3 & -OR4 &  AND5 & -OR6 & -AND7)


##----------------------------------------------------------------------------
## generate truth table for hierarchical decoding of AND-OR-AND...
## sequences, which pop up when comparing less-than-X; see
## satsolv_less_than_template_2x()
##
def cmp_truthtable(n):
	res = [ [ 0, 0, ] ] * (1 << n)

	for i in range(len(res)):
		ibits = f'{ i :0{n}b}'
		ib    = list(int(b)  for b in ibits)

		is_le, is_and = None, True
					## track hierarchical comparison
					## is_le set to True/False as soon
					## as known

		for f in ib:
			if is_le != None:
				break

			elif is_and:          ## NOT(AND) turns unknown into LE
				if (is_le == None) and (f == 0):
					is_le = True

			else:                 ## OR turns unknown into NOT(LE)
				if (is_le == None) and (f == 1):
					is_le = False

			is_and = not is_and               ## AND/OR's alternate

		is_le = (is_le == True)      ## None: compared equal -> NOT(LE)

		res[i] = [ ibits, is_le ]
		print(ibits, is_le)

	## print()
	for rbits, r in res:
		print(rbits + '.' +('1'  if r  else '0'))

	print()


##----------------------------------------------------------------------------
## returns:
##    1) AND/OR terms; list of operation strings
##    2) number of non-result variables added (AND/ORs, excluding shortcuts)
##    3) number of minimal added variables which may be reduced, see shortcuts
##    4) additional terms: expansion of AND/OR terms from (1)
##
## 'nvars' specifies input bit indexes 1..N
## 'drop_irrelevant' skips [trailing, OR] terms which can not influence
## ...V bits... < N comparison
##
## 'base' is first added, non-result variable to add
##
## shortcut:
##    - single AND term may be mapped to a NAND -> result is directly
##      used, does not need intermediate variable
##
## TODO: return SAT-template directly
##
## additional-term list:
##    [ +- ...index...       integer: original input variable
##         AND(...)/OR(...)  indirect term:
##              [8, [1, 3]]  AND()/OR() variable is 8; of original 1..3 inputs
##
def runs2terms(runs, nvars, base=1, drop_irrelevant=True):
			## all-1 runs turn into NAND(...) or just NOT(...)
			## all-1 runs turn into OR(...) or just (1 variable)

	seen, terms, addl, real, rv = 1, [], {}, 0, 0

	may_drop_or = (len(runs) & 1) == 0
			## trailing 0's never decide <...V...
			##   N<110  <=>  MS(N)<11, regardless of LS bit
			##   -> drop trailing-all-0 region from comparison

	for ri, r in enumerate(runs):
		if drop_irrelevant and may_drop_or and (ri >= (len(runs) -1)):
			break

		inputs, adds = f'{ seen }', 0
		if len(r) >1:
			inputs += f'..{ seen+len(r)-1 }'

		if r[0] == 1:                                   ## AND() or var
			if len(r) == 1:
				terms.append(seen)              ## AND(v) <=> v
			else:
				terms.append(f'AND({ inputs })')
				adds = 1
		else:
			if len(r) == 1:
				terms.append(seen)               ## OR(v) <=> v
			else:
				terms.append(f'OR({ inputs })')
				adds = 1

		if adds:
			if terms[-1] in addl:
				raise ValueError("AND/OR expression not unique")

			addl[ terms[-1] ] = [ base +len(addl),
			              [ seen, seen+len(r)-1 ], ]
		seen += len(r)
		rv   += adds

	return terms, rv, real, addl


##--------------------------------------
## recurring: append <(copy of) prefix | modified tail> to list of clauses
##
def arr2merged(prefix, tail):
	r = prefix[:]
	r.extend(tail)

	return r


##--------------------------------------
## hierarchical expressions to hierarchical decoder clauses
## of less-than-X comparison
##
## returns clauses, exact nr. of additional variables used
## first one is, if >0, the returned 'is-less-than(...)' variable
##
## runs on runs2terms() output
##
## input is alternating list of AND(...) OR(...) terms, or
## '=X' if variable 'X' is used directly (AND or OR of itself);
## 'result' True forces less-than-X to be True
##          False...             ...to be False
##
## non-0 'rvar' specifies the result variable (...may be negated...)
##
## see 'sample run-to-terms expansion' expansion for an example
##
## assume building AND and OR by default; we invert to NAND/NOR as necessary
##
def hterms2clauses(terms, nrvars, addl, rvar=0, result=None):
	cvars, clauses = [], []
	ands, ors = [], []

## TODO: centralized forced-to-... decoding
## TODO: generate NAND() directly to terms; skips reverse/spec.case here

				##--------------------------------------------
				## special case:
				## single AND term -> LT = NAND(...) directly
				##
				## replace direct-return variable: our
				## NAND requires no aggregator
				##
				## since trailing ORs are eliminated,
				## checking for 1 or 2 terms is exact
				##
				## 1-1-1-1 0-0-0-0  ->
				##    AND(1..4)     ->
				##    less-than(0xf0) == NAND(1..4)
				##

				## AND -> already collapsed to NOT(...)
	if (len(terms) < 2) and not addl:
				## any specialized processing would come here
		pass

	if (len(terms) < 2) and addl:
		aterm = terms[0]                   ## must be AND(...)
		assert(aterm.startswith('AND'))

		if satsolv_is_debug():
			print(f'## single-term AND -> NAND')

		if not aterm in addl:
			raise ValueError(f"unknown +term ({aterm})")

		if rvar == 0:
			rvar = nrvars +1           ## direct NAND == result
		else:
			assert(rvar == nrvars +1)  ## assumed +2 variables; only
			                           ## need +1, the NAND one
			## ensure setup expected exactly +1 AND term

		avs = addl[ aterm ][1][ -1 ]

				## note: watch out for indexes.  the run
				## of, f.ex. 0xff00 contains 8 bits (NAND(MS8))
				## while number of variables is 16
				## (so the assigned variable is from nr.vars)

		t = satsolv_and_template(avs, rvar=rvar, negate=True,
			        force = True  if (result == True)  else None)
				## any specialized log etc. would come here

		return t[ 'clauses' ], 1

	if rvar == 0:
		rvar = nrvars +len(addl) +1        ## aggregate result variable


			## collected AND/OR templates
	aotempls = []

	for ti, t in enumerate(terms):
		is_and = (ti & 1) == 0

		if isinstance(t, int):
			cvars.append(t)
		else:                         ## AND(...) or OR(...) expression
			if not (t in addl):
				raise ValueError(f"unknown +term ({r})")

			## addl[] entry: [ AND/OR variable nr.
			##                 [ min(), max() original inputs ] ]
			cvars.append(addl[t][0])

			imn, imx = addl[t][1][0], addl[t][1][1]

			ivars = list(range(imn, imx+1))
			curr  = cvars[-1]

			if 'AND' == t[:3]:
				aotempls.append(
					satsolv_and_template(ivars, rvar=curr))
## TODO: proper rebase
			elif 'OR' == t[:2]:
				aotempls.append(
					satsolv_or_template(ivars, rvar=curr))
## TODO: proper rebase
			else:
				raise ValueError("unknown term ({t})")

			## cvars[] is AND/OR/AND... index list
			## build alternating AND/OR/... expressions

	if (len(cvars) & 1) == 0:
		raise ValueError("invalid AND/OR/.../AND nesting")

	if satsolv_is_debug():
		print('## AND/OR templates', aotempls)

## hierarchical expressions (DNF):                                     <10101
##   -AND(1)                                        ->      less-than   0.... <
##    AND(1) &  OR(2)                               ->  NOT(less-than)  11...
##    AND(1) & -OR(2) & -AND(3)                     ->      less-than   100.. <
##    AND(1) & -OR(2) &  AND(3) &  OR(4)            ->  NOT(less-than)  1011.
##    AND(1) & -OR(2) &  AND(3) & -OR(4) & -AND(5)  ->      less-than   10100 <
##    AND(1) & -OR(2) &  AND(3) & -OR(4) &  AND(5)  ->  NOT(less-than)  10101
##
## note table regularity; since always AND/OR/AND... terms alternate,
## and the trailing one is AND, construction is straightforward.
##
## CNF terms with 'LT' as less-than variable (de Morgan conversion):
##                                               negated/AND condition:
##    AND(1)                                LT   0....
##   -AND(1) -OR(2)                        -LT   1.... .1...
##   -AND(1)  OR(2)  AND(3)                 LT   1.... .0... ..0..
##   -AND(1)  OR(2) -AND(3) -OR(4)         -LT   1.... .0... ..1.. ...1.
##   -AND(1)  OR(2) -AND(3)  OR(4)  AND(5)  LT   1.... .0... ..1.. ...0. ....0
##   -AND(1)  OR(2) -AND(3)  OR(4) -AND(5) -LT   1.... .0... ..1.. ...0. ....1
##
## TODO: simplified version with LT known to be True


	prefix = []     ## collect frozen part of the prefix expression
			##   '-AND(1) OR(2)'               then
			##   '-AND(1) OR(2) -AND(3) OR(4)'
			## in above example

					## last variable is special-cased below
					##
					## that is always an AND, so
					## we expand AND+OR pairs here
					## (1..4 in the above example)

## TODO: now already simplified to retrieve pairs-of-terms
## refactor with slice+map inner loop

	for ci in range((len(cvars) -1) // 2):
		ltvar = sat_not(rvar)  if  (ci & 1)  else rvar
				## LT variable with proper non/negation state

							## AND/OR variables
		and_var, or_var = cvars[ ci*2 ], cvars[ ci*2 +1 ]

				##   '-AND(1) OR(2)'               then
				##   '-AND(1) OR(2) -AND(3) OR(4)'

## TODO: check for reference-breaking property of .append()
## (which is probably documented); MUST capture current value
## prefix[] since it is extended right after adding clauses

							##  AND(1)         LT
		clauses.append( arr2merged(prefix, [ and_var, rvar ]) )
							## -AND(1) -OR(2) -LT
		clauses.append( arr2merged(prefix,
			[ sat_not(and_var), sat_not(or_var), sat_not(rvar) ]) )

		prefix.extend([ sat_not(and_var), or_var, ])

## now the final clause pair:
##   -AND(1)  OR(2) -AND(3)  OR(4)  AND(5)  LT   1.... .0... ..1.. ...0. ....0
##   -AND(1)  OR(2) -AND(3)  OR(4) -AND(5) -LT   1.... .0... ..1.. ...0. ....1

	and_var = cvars[-1]

	clauses.append( arr2merged(prefix, [ and_var, rvar ]) )
	clauses.append( arr2merged(prefix,
				[ sat_not(and_var), sat_not(rvar) ]) )

	for ai, at in enumerate(aotempls):                  ## now base clauses
		for c in at[ 'clauses' ]:
			clauses.append(c)

	return clauses, len(addl) +1


##--------------------------------------
## sample run-to-terms expansion:
##     RUNS(118)=[[1, 1, 1], [0], [1, 1], [0]]         original variables: 1..7
##     ->
##     AND/OR TERMS ['AND(1..3)', 4, 'AND(5..6)']
##         +2V {'AND(1..3)': [8, [1, 3]], 'AND(5..6)': [9, [5, 6]]}
##
## note that last [0] is dropped: it would be an OR term which never
## decides less-than. (trailing OR run would only matter if less
## significant all-1's run could follow.)
##
## hierarchical expressions (DNF):                                     <10101
##   -AND(1)                                        ->      less-than   0.... <
##    AND(1) &  OR(2)                               ->  NOT(less-than)  11...
##    AND(1) & -OR(2) & -AND(3)                     ->      less-than   100.. <
##    AND(1) & -OR(2) &  AND(3) &  OR(4)            ->  NOT(less-than)  1011.
##    AND(1) & -OR(2) &  AND(3) & -OR(4) & -AND(5)  ->      less-than   10100 <
##    AND(1) & -OR(2) &  AND(3) & -OR(4) &  AND(5)  ->  NOT(less-than)  10101
##
## note table regularity; since always AND/OR/AND... terms alternate,
## and the trailing one is AND, construction is straightforward.
##
##
## CNF terms with 'LT' as less-than variable (de Morgan conversion):
##                                               negated/AND condition:
##    AND(1)                                LT   0....
##   -AND(1) -OR(2)                        -LT   1.... .1...
##   -AND(1)  OR(2)  AND(3)                 LT   1.... .0... ..0..
##   -AND(1)  OR(2) -AND(3) -OR(4)         -LT   1.... .0... ..1.. ...1.
##   -AND(1)  OR(2) -AND(3)  OR(4)  AND(5)  LT   1.... .0... ..1.. ...0. ....0
##   -AND(1)  OR(2) -AND(3)  OR(4) -AND(5) -LT   1.... .0... ..1.. ...0. ....1
##
## simplified versions if result is known:
## (1) result is True  ->
## TODO: simplified version with LT known to be True
##
## simplified versions if result is known, LT is True:
##    AND(1)                                LT   0....
##   -AND(1) -OR(2)                        -LT   1.... .1...
##   -AND(1)  OR(2)  AND(3)                 LT   1.... .0... ..0..
##   -AND(1)  OR(2) -AND(3) -OR(4)         -LT   1.... .0... ..1.. ...1.
##   -AND(1)  OR(2) -AND(3)  OR(4)  AND(5)  LT   1.... .0... ..1.. ...0. ....0
##   -AND(1)  OR(2) -AND(3)  OR(4) -AND(5) -LT   1.... .0... ..1.. ...0. ....1


##----------------------------------------------------------------------------
## expressions compare up to two runs' worth of bits
## 'nvars' is 1..N for N-bit input
##
## 'result' True forces less-than-X to be True
##          False...             ...to be False
##          None                 assigns new variable to result
##
## first run always from an all-1 region
##
## returns clauses, comparison variable, comment.  beneath the variable:
##   (1)  AND( bits in leading/all-1 run)
##   (2)  OR( bits of trailing/all-0 run)
## the (2) return value may be None, if no trailing-0 is present
## any additional variables are registered to 'sat'
##
## comparison is hierarchical:
##   (1) if not-AND(1), value < ...constant..., as leading run < ...constant...
##   (2) if OR(2), value > ...constant...        unless (1) decided
##   (3) if not-AND(3), value < ...constant...   unless (1) or (2) decided
##
## 'runs' in the above cases: [ [1],        [0,0,...0,0]   ... ]
##                            [ [1,1,1,...,1]              ... ]
##                            [ [1,1,..,1], [0,0,0,...0,0] ... ]
## 'nbits' is the printable-collapsed form, 100..00, 111..111 etc., of
## the constant which is being compared against
## 'nvars' are the variables which form the comparison value
## 'result' True  ensures result is True
##          None  no restriction
##          False (currently not supported)
##
## 'rvar' (return variable) assigned to 1st added variable if not specified
##
## returns None, None, None  if no more runs
## registers any intermediate variables
##
## MAY CHANGE 'runs'
##
def satsolv_less_than_template_2x(nvars, runs, nbits, rvar=0, result=None,
                                  descr=None):
	if runs == []:
		return None, None, None

	if runs[0][0] != 1:
		raise ValueError("bits<N did not start with all-1 bit run")

	if (result != None) and (result != True):
		raise ValueError("bits<N can not force '{ force }' result")

	if rvar == 0:
		rvar = nvars +1
		if satsolv_is_debug():
			print(f"## RETURN->{ rvar }")

	terms, rv, shortcuts, addl = runs2terms(runs, nvars, base=rvar+1)
	if satsolv_is_debug():
		print('## AND/OR TERMS', rv, terms, f'+{ len(addl) }V', addl)

				## single term is always AND originally
				## -> turns into NAND, without any extra
				## variable
				##
	if addl and (len(terms) == 1):
		assert(terms[0].startswith('AND'))
		assert(len(addl.keys()) == 1)

	cls, avars = hterms2clauses(terms, nvars, addl, rvar=rvar,
	                            result=result)

	print(f'## CLAUSES.ORIG[{ len(cls) }]', cls)
	if result == True:
		print(f'## FORCED[var={ rvar }]')
		c2 = clauses_specialize(cls, rvar)
		if c2:
			print(f'## CLAUSES.FORCED[{ len(c2) }]', c2)
			cls = c2
		avars -= 1            ## del fixed variable (was 1st added one)

	print(f'## LEN(RUNS)={ len(runs) }')

	vdescr = f'## VARS:1..{nvars}'

	if len(vars) < len(runs[:2]):
		raise ValueError("not enough Booleans for less-than-N-2x")

	opr = 'LTF'  if (result == True)  else 'LT'

	xcomm = descr  if descr  else f'{ opr }({ nvars }b)'

	return cls, result, xcomm, avars


## ##----------------------------------------------------------------------------
## ## are the values equal, or either one is all-0?
## ## forces to different-or0 with 'force'
## ##
## ## comparison for check "are A and B equal, or is at least one of them
## ## unassigned?" if all-0 is reserved for unassigned
## ##
## ## turns into
## ##    -NOR(v1) AND -NOR(v2) -> NOT-EQ(v1, v2)
## ##
## ## XXX remove the rest
## ##    NOR(v1) | NOR(v2) | NOT-EQ(v1, v2)
## ##    <->
## ##    NOR(v1) | NOR(v2) | OR(XOR(v1, v2))
## ##
## ## single-bit version simplifies to
## ##    NAND(v1, v2)     -- only the 1/1 pair is invalid
## ##
## ## returns list of clauses, result variable, comment
## ##
## def satsolv_neq_or0(sat, v1, v2, result=None, force=False):
## 				## TODO: OR extra bits which are
## 				## in v1 or v2 only -> extra term in top clause
## 				## (all our current uses are identical-sized)
## 	if len(v1) != len(v2):
## 		raise ValueError("NEQ-OR0(...different sized vectors...")
## 
## 	rvar = 0
## 	if result == None:
## 		result = sat_new_varname2(sat, prefix='NEQ_OR0')
## 		rvar += 1
## 
## 	if len(v1) == 1:
## 		nv  = sat_new_varname2(sat, prefix='NAND')
## 		cmt = 'NEQ-OR0({ v1[0] } / { v2[0] }) -> NAND'
## ## TODO: proper piping/comment reporting
## 		return satsolv_nand1(x, y, result=nv)
## 
## 	nor1 = sat_new_varname2(sat, prefix='NOR')
## 	nor2 = sat_new_varname2(sat, prefix='NOR')
## 		##
## 	cls,  _, _ = satsolv_or('', v1, negate=True, result=nor1)
## 	cls2, _, _ = satsolv_or('', v2, negate=True, result=nor2)
## 		##
## 	cls.extend(cls2)
## 				## NOR(v1), NOR(v2)
## 
## 	xvars = []
## 				## XOR(...bits of v1..., ...bits of v2...)
## 				##
## 	for x, y in zip(v1, v2):
## 		xv = sat_new_varname2(sat, prefix='XOR')
## 
## 		cls3, _, _ = satsolv_xor1(x, y, result=xv)
## 		cls.extend(cls3)
## 		xvars.append(xv)
## 
## 				## OR(...above XOR bits...)
## 				## -> 1 if any XOR is 1 -> at least 1 bit diff
## 				## -> NOT-EQ(...)
## 				##
## 	neq = sat_new_varname2(sat, prefix='NEQ')
## 	cls4, _, _ = satsolv_or('', xvars, result=neq)
## 
## 	cls.extend(cls4)
## 
## ##	if result == None:
## ##		result = sat_new_varname2(sat, prefix='NEQ_OR0')
## 
## 				## NOR(1) NOR(2) OR(XOR(...)) -> NEQ-OR0
## 				##
## 	cls5, _, _ = satsolv_or('', [ nor1, nor2, neq ], result=result)
## 
## 	cls.extend(cls5)
## 
## 	if force:
## 		cls.append(satsolv_const(result))
## 
## 	cmt = f'NEQ-OR0[{ len(v1) }b]({ ",".join(v1) } / { ",".join(v2) })'
## 
## 	return cls, result, cmt


##----------------------------------------------------------------------------
## is the binary combination of 'vars' < N?
## return template with
##
## 'vars' inputs are used, 1..M; 'N' is forced to M-bit representation
##
## 'result' True forces less-than-X to be True
##          False...             ...to be False
##
## registers any newly allocated variables to 'sat'
##
## TODO: proper binary comparison, then Quine McCluskey etc. reduction
## TODO: right now, we just pick predefined patterns
##
def satsolv_less_than_template(sat, nvars, n, rvar=0, result=None):
	nbits = f'{ n :b}'
	nb    = list(int(b)  for b in nbits)

	if (n < 1):
		raise ValueError("out of range less-than({n})")

	if len(nbits) > nvars:                 ## N is wider than 2^...bits...
		return                         ## always succeeds

	runs = arr2runs(nb)

	assert(runs != [])
	assert(runs[0][0] == 1)                ## nb[] has no MS zeroes

	if satsolv_is_debug():
		print(f'## RUNS({n}/x{n:x}/{ n.bit_length() }b)={ runs }')

	cls, result, xcomm, addl = satsolv_less_than_template_2x(nvars,
	                               runs, nbits, rvar=rvar, result=result,
	                               descr=f'LT({n})')

		## ...any special logging etc. would happen here...

	t = template0(f'LT({n})', inputs=nvars)

## TODO: check list; auto-assign
	t[ 'add.vars' ] = addl
	t[ 'result'   ] = rvar
	t[ 'clauses'  ] = cls

	return t


##----------------------------------------------------------------------------
## filter out comment-only constraints, which do not lead to clauses
## comment-only conditions are empty strings for non-comment part
##
def sat_nr_clauses(sat):
	if (not sat) or (not "constraints" in sat):
		return 0

	nrc = sum(1  if (c[0] != '')  else  0
	          for c in sat[ "constraints" ])
	return nrc


##----------------------------------------------------------------------------
## count raw, numeric-only/expanded clauses
## rough equivalent of sat_nr_clauses()
##
def sat_clauses_count(cls):
	return sum(1  for c in cls  if (c != []))


##--------------------------------------
## print 'VAR.NAME(index)' pairs as SAT comments
##
## do not change VARIABLES framing
## or update dev/sat2back.py too
##
def sat_report_vars(sat, prefix=sSATPREFIX):
	vstr = ' '.join(f'{ v }[{ vi+1 }]'
	                for vi, v in enumerate(sat[ "vars" ]))

					## do not change VARIABLES framing
					## or update dev/sat2back.py too
	print(prefix +'c VARIABLES:')

	for v in textwrap.wrap(vstr, width=64):
		print(prefix +'c   ' +v)

	print(prefix +'c /VARIABLES')
	print(prefix +'c')


##--------------------------------------
def satsolv_report(sat):
	if not use_satsolver():
		return

	nrclauses = sat_nr_clauses(sat)

					## problem sizes
	print(sSATPREFIX + f'p cnf { len(sat[ "vars" ]) } { nrclauses }')

	print(sSATPREFIX +'c')
	print(sSATPREFIX +'c CONSTRAINTS:')
					## do not change CONSTRAINTS framing

	comments = 0
	for commstr in (s  for s in sat[ "constraints" ]  if s[1]):
		if commstr:
			print(sSATPREFIX +'c   ' +commstr[1])
			comments += 1

	print(sSATPREFIX +'c /CONSTRAINTS')
	print(sSATPREFIX +'c')

	sat_report_vars(sat)

					##-----  end of header  --------------

	for ci, c in enumerate(sat[ "constraints" ]):
		cvars, comment = c[0], c[1]

		if cvars.strip() == '':
			continue
					## map expression to int. indexes
					## each entry MUST be present
					##
		if cvars[ : len(sSAT_SYM_PREFIX) ] == sSAT_SYM_PREFIX:
			constr = cvars[ len(sSAT_SYM_PREFIX): ].split()
			constr = " ".join(str(s) for s in
			                  satsolv_vars2ints(sat, constr))

		else:
			constr = " ".join(str(sat[ "vars" ].index(v) +1)
			                  for v in cvars.split())

		print(sSATPREFIX +constr +sSAT_CONSTR_END)

	print()


##============================================================================
## 2xN bits, v1[] and v2[]
## return list of bitpair-wise XORs' variables; clauses
## rbase is index of first XOR-result variable
##
## ORed together: v1[] != v2[]
##
def satsolv_diff_template(v1, v2, result=0, rbase=0):
	t1, t2 = list(v1), list(v2)
	if len(t1) != len(t2):
		raise ValueError(f"DIFF(..) input lengths differ ({t1},{t2})")

## TODO: sync all template-construction fns' prototypes

	assert(max(len(t1), len(t2)) > 0)

	res = template0(f'DIFF({ len(v1) })', len(v1)*2)

	## additional vars:
	##   <result>  XOR(1)  XOR(2) ... XOR(N)   OR
	##             XOR(1)  XOR(2) ... XOR(N)   OR

	addr = 0
	if result == 0:
		result = 2 * len(t1) +roffs
		rbase  = result +1
		addr   = 1
	elif rbase == 0:
		rbase = 2 * len(t1) +1

						## constituent XORs
	xorvars = [ (v + rbase + 1)  for v in range( len(t1) ) ]

	if len(t1) == 1:
		print('## DIFF(1)->XOR(1)', t1, t2)
		return satsolv_xor1_template(t1[0], t2[0], rv = result,
		                             descr='DIFF(1)->XOR(1)')

	clauses = []

	print('## XOR(pair) variables:', xorvars)

	orx_t = satsolv_or_template( xorvars, rvar=result )
	                                             ## OR(...XOR variables...)

	for v in range(len(t1)):
		res[ 'clauses' ].extend(satsolv_xor1_template(v+1, v+1+len(t1),
                                    rv = xorvars[ v ])[ 'clauses' ])

	res[ 'add.vars'   ] = len(xorvars)
	res[ 'result'     ] = xorvars[0]
	res[ 'clauses'    ].extend(orx_t[ 'clauses' ])
	res[ 'outputs'    ].append( xorvars[0] )
	res[ 'nr.outputs' ] = len(res[ 'outputs' ])
## TODO: do we have centralized macros for these?

	template_sync(res)

	return res


##============================================================================
## assume (1..vars) and (vars+1..2*vars), inclusive, are all inputs
## 2*vars+1 is response variable
##
## TODO: merge into satsolv_neq_or0() which has the rest of logic already
##
## with True 'non0', we also ensure they are all non-0 (so forcing them
## to be different since all >0)
##
## 'or1' or 'or2', when not 0, supply OR(..var1[]..) or OR(..var2[]..),
## respectively
##
## 1) build OR(...) for both inputs (OR1, OR2)
## 2) build per-pair XORs, with "-OR1 -OR2 ..." added: NOR1 or NOR2 sets True
## 3) NOR(1) NOR(2) OR(XOR(...))  <->  result
##
def satsolv_noneq0_template(vars, result=None, non0=True, force=False,
                            or1=0, or2=0):
	sat      = satsolv_init0()
	clauses  = []
	var_nadd = 0           ## how many 'intermediate' variables are not new
	addvs    = 0
## TODO: check TODOs below; these vars become redundant

	if result == None:
		result = 2* vars +1 +(2  if or1  else 0)
		addvs  += 1

## TODO: merge into satsolv_neq_or0() which has the rest of logic already
	if vars == 1:
		res = satsolv_and_template(2, rvar=result,
		                           negate=True, force=force)
		if or1:
			res[ 'inputs' ] += 2                        ## two OR's
		print(f"## TEMPLATE(FINAL) r={ result }", res)
		return res

	varidx = { 'NEQ0': result }

	addl = [ { varidx[ "NEQ0" ] : "final NEQ0 result" }, ]
				## first entry: output bit

				## [-1].keys() has a single element; list()
				## forces order. otherwise:
				##     TypeError: 'dict_keys' object is
				##     not subscriptable
				##
				## TODO: check version-portable proper type
## TODO: list() indirection is horrible; check for proper dict_keys()
## type conversion

	if or1 == 0:
		or1nv = varidx[ 'NEQ0' ] +1
		or2nv = or1nv +1
		addl.append({ or1 : f"OR(1..{vars})"                })
		addl.append({ or2 : f"OR({vars+1}..{vars*2})"       })

		varidx[ 'OR1' ] = or1nv
		varidx[ 'OR2' ] = or2nv
		orx = or2nv +1
		addvs += 2
	else:
		varidx[ 'OR1' ] = or1
		varidx[ 'OR2' ] = or2
		orx = varidx[ 'NEQ0' ] +1

	varidx[ 'DIFF' ] = orx
	addvs += 1

	rbase = orx +1                        ## start of subordinate variables

	if result:
		var_nadd += 1

	addl.append({ orx : f"OR(...XOR(1)..XOR({vars})..)" })

	if or1 == 0:
		or_t  = satsolv_or_template(vars)
				## rebase to OR1 variable = or1nv (above)
		or1avars = or1nv - vars - or_t['add.vars']

		or_t  = template_rebase(or_t,
		                 addl_vars = or1nv - vars - or_t['add.vars'])

		or2_t = satsolv_or_template(vars)
				## rebase to OR2 variable = or2nv (above)
		or2avars = or2nv - 2*vars - or2_t['add.vars']

		or2_t = template_rebase(or2_t, vars=vars,
		                 addl_vars = or2nv - 2*vars - or2_t['add.vars'])

		print(f"## OR(1) +{ or1avars }.VARS")
		print(f"## OR(2) +{ or2avars }.VARS")
	else:
		print(f"## OR(1)={ or1 }, OR(2)={ or2 }")
##
## TODO: sync, either append all to addl[], or track _nadd
##		var_nadd = 0

## XOR(...pairs...) + OR(...XOR's...)

	print('## NONEQ-OR-0 mappings:', varidx)

	diff_t = satsolv_diff_template(range(vars), range(vars+1, vars*2 +1),
	                               result=varidx[ 'DIFF' ], rbase = rbase)
	print(f'## OR(XOR[{ vars }])', diff_t)

	addl.extend({ rbase +x : f'XOR({x})' }
	            for x in range(diff_t[ 'add.vars' ]))
	addvs += vars                              ## XOR(.) for each input bit

	if or1 == 0:
		cls = or_t[ 'clauses' ]
		append_clauses(cls, or2_t)
	else:
		cls = []

	append_clauses(cls, diff_t)
#	for xc in xorcls:
#		append_clauses(cls, diff_t)

## TODO: need a wrapper to simplify stacked rebases
			## XOR(...var1..., ...var2...) -> OR(...) <=> NOT-EQUAL
			## NEQ-OR0 clause:
			##     R = ( NOR(1)  or  NOR(2)  or  OR(...XORs...) )
			##
	if or1 == 0:
		full = satsolv_or_template([ sat_not(or1nv), sat_not(or2nv),
		                             orx ], rvar = result)
	else:
		full = satsolv_or_template([ sat_not(or1), sat_not(or2),
		                             orx ], rvar = result)
	cls.extend(full[ 'clauses' ])

	type = 'NEQ0' + ('.FORCE'  if force  else '')

	print('## ADD.VARS(NEQ0)', len(addl), addl)
	print('## -ADD.VARS', var_nadd)

			## all paths MUST be consistent
	assert(len(addl) >= var_nadd)

	instr = f'2x ({vars} +1)'  if or1  else f'2x {vars}'

	res = template0(f'NEQ0({ instr })', vars *2 +(2  if or1  else 0))
	##
## TODO: check that all sub-templates properly account for result/or1/or2,
## then derive from those

	res[ 'add.vars' ] = addvs                       ## len(addl) - var_nadd
	res[ 'result'   ] = result
	res[ 'clauses'  ] = cls

	maxvarnr = clauses_max_varnr(cls)
	print(f'## MAX(VARNR)={ maxvarnr }')

	if force:
		print(f"## TEMPLATE(ORIG) r={ result }", res)
		list_clauses(res[ 'clauses' ])
		print("## /TEMPLATE(ORIG)")
		template_specialize(res, result, val=True, addl=False)
				## addvs already adjusted for result != 0

		maxvarnr = clauses_max_varnr(res[ 'clauses' ])
		print(f"## TEMPLATE(FINAL) r={ result }", res)

	return res


##--------------------------------------
vFULLTEMPLATE_HDR_ENTRIES = 4   ## fixed prefix in table-of-templates
vTEMPLATE_HDR_ENTRIES = 4       ## fixed prefix in each template
                                ## at least this many units are present

vTEMPLATE_ADDL_BITS   = 2       ## in-band bits: negative; additional var;
vCLAUSE_TERMINATOR    = 0       ## make markers explicit

		## identifier of above in generated C source
sCNF_TEMPLHDR_ID = 'CNF_TEMPLATEHDR_ELEMS'

## defined variables: replace prefix:
##   #define  SAT_TEMPL_1_OF_N=23_IS_NEGATIVE  UINT8_C(0x80)
##   #define  SAT_TEMPL_1_OF_N=23_IS_ADDED_VAR UINT8_C(0x40)
##            ^^^^^^^^^^^^^^^^ prefix, up to ...N=23
##
##   static const uint8_t __TEMPL__1_OF_N=23__[286] = {
##                        ^^^^^^^^^^^^^^^^^ prefix, up to ...N=23


##--------------------------------------
## given text clauses, input (V) plus added intermediate (A) variables,
## turn clause list into template:
##     (1) input variables are numbered 1..V
##     (2) intermediate variables are numbered V+1..V+A
##
## 'result' MUST be one of variables if not ''; if it is an intermediate one,
## it will be assigned index V+1
##     TODO: multi-valued variant, where this is a list
##
## 'raw' selects text-encoded raw clauses ('1 2 3
##
## returns [ [ clauses1 ], [ clauses2 ], ... ], total elem.count,
##           nr. of clauses, nr. added variables (A), max.variables
##           (worst-case clause), unit.bitcount
##
## TODO: return proper dict/struct
##
## elem.count includes 0-padding, plus header:
##     (1) nr. of input variables (V)
##     (2) nr. of added/intermediate variables (A)
##     (3) max nr. of variables in worst-case clause (excluding terminating 0)
##     (4) terminator, now reserved-0
## see vTEMPLATE_HDR_ENTRIES
##
## all values padded to uniform width which accommodates MAX(V,A) plus two bits
##     x8...  ->  index is negated (<0)
##     x4...  ->  index of added/intermediate variable
## LS bits are actual variable index, >0
##
## compact >1  squeezes out all whitespace
##          1  adds spaces, not newlines, between clause list
##          0  one clause per line
##
## note: not taking already-populated SAT state, since it may contain
## other variables/clauses---for example: multiple instances of
## functions of the same varaible. we construct exact list of of
## additional variables not in 'vars'
##
def clauses2template(cls, vars, nvars, result, raw=True):
	sv, snv = set(vars), set(nvars)

	if len(sv) != len(vars):
		raise ValueError("non-unique input list")
	if len(snv) != len(nvars):
		raise ValueError("non-unique intermediate-variable list")

## TODO: union, check size vs. union(vars+nvars)

	s = satsolv_init0()

	satsolv_add_vars(s, vars)
##	for nv in nvars:
##		satsolv_add_1var(s, nv)

	if (result != '') and (result != []):
		satsolv_add_vars(s, [ result ])         ## NOP if one of inputs

	if raw:
		addvars = list(a  for a in satsolv_clauses2ids(cls)
		               if (not a in vars))
	else:
		addvars = list(range(len(vars), len(vars) + len(nvars)))

	satsolv_register_added_vars(s, len(addvars))

	satsolv_add_vars(s, list(a  for a in addvars  if (a != result)))
					## ID-to-index lookup, 1..V, V+1..V+A

					## nr. of bits(integers) +sign(1)
					## +is-added-variable?(1)
					##
	intbits = len(s[ 'vars' ]).bit_length() +2
					## ideally, this is exactly V+A
					## in other words, >= MAX(V, A)

	intbits = ((intbits +7) //8) *8                    ## pad to full bytes

	intxdigits = ((intbits //8) * 2)

	res, maxcvars = [], 0

			## constants to mark variables, aligned to MS(intbits)
			##   0x8...  variable is negated (<0)
			##   0x4...  added/intermediate, not input variable
			##
	neg    = 1 << (intbits -1)
	added  = 1 << (intbits -2)

	fmt0 = f'0x{ 0 :0{intxdigits}x}'

	## build normalized clause frames
	## raw:
	##
	## non-raw (example: less-than templates):
	## - indexes already numeric
	## - need only num-to-table conversion
	##   LT(1) {'descr': 'LT', 'inputs': 1, 'add.vars': 0, 'result': 1,
	##       'in.base': 0, 'add.base': 0, 'clauses': [[1, 2], [-1, -2]],
	##       'comments': []}

	##--------------------------------------------------------------------
	for c in cls:
## TODO: recurring, factor out all 'if raw...' paths
		if raw:
			signs, ids = satsolv_str2ids(c.split())
						## keep ints >0
						## append sign separately
			ints = list(satsolv_vars2ints(s, [ i ])[0]
			            for i in ids)
		else:
			ids   = list(abs(v)  for v in c)
			ints  = ids[:]
			signs = list(('-'  if (v<0) else '')  for v in c)

		res.append([])

						## pretty-print
		pprint = (f"{ sig }{ id }[{ i }]"  for sig, id, i
		          in zip(signs, ids, ints))

		print('//', " ".join(pprint))

				## signs, ids, ints of uniform element count
				## ('-' or ''); name; variable index>0

		for sig, id, i, idx in zip(signs, ids, ints, range(len(ints))):
				## set extra bits
				##
			r = 0  if (sig == '')  else neg

## TODO: track variable type, turn into base-index

			if (i > len(vars)):     ## added variable ->
				                        ## rebase to 1..A
				i -= len(vars)  ## ADDED(0) -> abs. 1
				r |= added

					## MS bits MUST NOT conflict with index
			r = f'0x{ r+i :0{intxdigits}x}'

			res[-1].append(r)

		maxcvars = max(maxcvars, len(ids))
		res[-1].append(fmt0)

				## do not expect this with sane data:
				## _lots_ of clauses with few variables
				##
	if (maxcvars > neg):
		raise ValueError("nr. of clauses does not fit bitwidth")

		## lead/header: total nr. of entries, nr. of inputs
		##
	res.insert(0, [ f'0x{ len(vars)    :0{intxdigits}x}',
	                f'0x{ len(addvars) :0{intxdigits}x}',
	                f'0x{ len(cls)     :0{intxdigits}x}',
	                f'0x{ maxcvars     :0{intxdigits}x}', ])

	units = sum(len(r)  for r in res)

	return res, units, len(cls), len(res), len(addvars), maxcvars, intbits


##--------------------------------------
## given clauses, input (V) plus added intermediate (A) variables, turn clause
## list into template:
##   (1) symbolic templates
##     (1) input variables are numbered 1..V
##     (2) intermediate variables are numbered V+1..V+A
##   (2) numeric templates  <->  'vars' and 'nvars' are integers
##     -> only numeric expressions
##
## see templ2c() for cases where template has already been fully
## processed
##
## 'result' MUST be one of variables if not ''; if it is an intermediate one,
## it will be assigned index V+1
##   - if True or False, results are forced and not assigned to a variable
## TODO: multi-valued variant, where this is a list
##
## returns [ [ clauses1 ], [ clauses2 ], ... ], total elem.count,
##           nr. of clauses, nr. added variables (A), max.variables
##           (worst-case clause), unit.bitcount
##
## TODO: return proper dict/struct
##
## elem.count includes 0-padding, PLUS HEADER:
##     (1) nr. of input variables (V)
##     (2) nr. of added/intermediate variables (A)
##     (3) nr. of clauses
##     (4) max nr. of variables in worst-case clause (excluding terminating 0)
## see vTEMPLATE_HDR_ENTRIES
##
## all values padded to uniform width which accommodates MAX(V,A) plus two bits
##     x8...  ->  index is negated (<0)
##     x4...  ->  index of added/intermediate variable
## LS bits are actual variable index, >0
##
## compact >1  squeezes out all whitespace
##          1  adds spaces, not newlines, between clause list
##          0  one clause per line
##
## note: not taking already-populated SAT state, since it may contain
## other variables/clauses---for example: multiple instances of
## functions of the same varaible. we construct exact list of of
## additional variables not in 'vars'
##
def clauses2params(cls, vars, nvars, result, raw=True, unitbits=0):
	sv  = set(vars)
	snv = set(nvars)

	if len(sv) != len(vars):
		raise ValueError("non-unique input list")
	if len(snv) != len(nvars):
		raise ValueError("non-unique added-variable list")

## TODO: union, check size vs. union(vars+nvars)

	s = satsolv_init0()

	satsolv_add_vars(s, vars)
		##
##	for nv in nvars:
##		satsolv_add_1var(s, nv)

	if ((result != '') and (result != []) and (result != True) and
	    (result != False)):
		satsolv_add_vars(s, [ result ])         ## NOP if one of inputs

	if raw:
		addvars = list(a  for a in satsolv_clauses2ids(cls)
		               if (not a in vars))
	else:
		addvars = list(range(len(vars), len(vars)+len(nvars)))

	satsolv_register_added_vars(s, len(addvars))

	satsolv_add_vars(s, list(a  for a in addvars  if (a != result)))
					## ID-to-index lookup, 1..V, V+1..V+A

					## nr. of bits(integers) +sign(1)
					## +is-added-variable?(1)
					##
	intbits = len(s[ 'vars' ]).bit_length() +vTEMPLATE_ADDL_BITS
					##
					## ideally, this is exactly V+A
					## in other words, >= MAX(V, A)

	intbits = ((intbits +7) //8) *8                    ## pad to full bytes

	intxdigits = ((intbits //8) * 2)

	res, maxcvars = [], 0

			## constants to mark variables, aligned to MS(intbits)
			##   0x8...  variable is negated (<0)
			##   0x4...  added/intermediate, not input variable
			##   0x2...  last variable of clause
			##
	neg    = 1 << (intbits -1)
	added  = 1 << (intbits -2)

	fmt0 = f'0x{ 0 :0{intxdigits}x}'

	for c in cls:
		if raw:
			signs, ids = satsolv_str2ids(c.split())
						## keep ints >0
						## append sign separately
			ints = list(satsolv_vars2ints(s, [ i ])[0]
			            for i in ids)
		else:
			ids   = list(abs(v)  for v in c)
			ints  = ids[:]
			signs = list(('-'  if (v<0) else '')  for v in c)

		res.append([])

						## pretty-print
		pprint = (f"{ sig }{ id }[{ i }]"  for sig, id, i
		          in zip(signs, ids, ints))

		print('//', " ".join(pprint))

				## signs, ids, ints of uniform element count
				## ('-' or ''); name; variable index>0

		for sig, id, i in zip(signs, ids, ints):
				## set extra bits
				##
			r = 0  if (sig == '')  else neg

## TODO: track variable type, turn into base-index

			if (i > len(vars)):          ## added variable ->
			                             ## rebase to 1..A
				i -= len(vars)       ## ADDED(0) -> absolute 1
				r |= added

				## MS bits MUST NOT conflict with index
			r = f'0x{ r+i :0{intxdigits}x}'

			res[-1].append(r)

		maxcvars = max(maxcvars, len(ids))
		res[-1].append(fmt0)

				## do not expect this with sane data:
				## _lots_ of clauses with few variables
				##
	if (maxcvars > neg):
		raise ValueError("nr. of clauses does not fit bitwidth")

		## lead/header: total nr. of entries, nr. of inputs
		##
	res.insert(0, [ f'0x{ len(vars)    :0{intxdigits}x}',
	                f'0x{ len(addvars) :0{intxdigits}x}',
	                f'0x{ len(cls)     :0{intxdigits}x}',
	                f'0x{ maxcvars     :0{intxdigits}x}', ])
## TODO: use template2hdr()
		##
		## appends vTEMPLATE_HDR_ENTRIES elems

	units = sum(len(r)  for r in res)

	return res, units, len(cls), len(res), len(addvars), maxcvars, intbits




##--------------------------------------
## generate C constant table for template
##
## if 'nvars' is integer, 'cls' MUST be already a Template; we
## only use number of variables
## (see 'Symbolic template' for struct)
##
## 'r' is name of output Boolean, which will be assigned as 1st add'l variable
## if True or False, results are forced and not assigned to a variable
##
## 'tid' is template ID, string to include in C definitions
##
## TODO: multi-valued output MUST accommodate list
##
## TODO: merge back clauses2print() and clauses2template()
##
def clauses2print(cls, vars, nvars, r, tid, raw=True, instance=None,
                  unitbits=0):

	if unitbits == 0:
		unitbits =  (len(vars) + len(nvars)).bit_length()
		unitbits += vTEMPLATE_ADDL_BITS
	unitbits = next_power2(unitbits)

	ct, ccnt, nrcls, units, addvars, maxv, cbits = clauses2params(cls,
	                 vars, nvars, result=r, raw=raw, unitbits=unitbits)
	nrvars = len(vars)

	if len(ct[0]) != vTEMPLATE_HDR_ENTRIES:
		raise("first clause->template does not look like header")

	ctype = print_ctemplate_hdr(cbits)

	if instance == None:
		instance = len(vars)

	print(f'// CLAUSES[TYPE={ ctype }]' +
		f'[{ nrvars }+{ addvars }(x{ nrvars :x}+' +
		f'x{ addvars :x})({ nrvars +addvars }/' +
		f'x{ nrvars +addvars :x}) variables]' +
		f'x[max { maxv } vars/cls]:')

	negbit, addvbit = markbits(unitbits)
	maskbits = min(negbit, addvbit) -1

## TODO: sync clause-to-print etc. heuristics

	vprefix = f'SAT_TEMP_{ tid }{ instance }'

				## bit width, masking macros
	print("/**/")
	print(f'#define  { vprefix }_MASK          ' +
			f'UINT{ cbits }_C(0x{ maskbits :x})')
		##
	print(f'#define  { vprefix }_IS_NEGATIVE   ' +
			f'UINT{ cbits }_C(0x{ negbit :x})')
		##
	print(f'#define  { vprefix }_IS_ADDED_VAR  ' +
			f'UINT{ cbits }_C(0x{ addvbit :x})')
	print("/**/")

## TODO: pick up align-columns from multiply-carpet generator

	print(f'#define  { vprefix }_INPUT_VARS      ' +
			f'((unsigned int) { nrvars })')
	print(f'#define  { vprefix }_ADDL_VARS       ' +
			f'((unsigned int) { addvars })')
	print(f'#define  { vprefix }_CLAUSES         ' +
			f'((unsigned int) { nrcls })')
	print(f'#define  { vprefix }_MAX_CLS_VARS    ' +
			f'((unsigned int) { maxv  })')
	print(f'#define  { vprefix }_MAX_CLSVARS_USE ' +
			f'((unsigned int) { maxv * nrcls })')
	print(f'#define  { vprefix }_VARBITS         ' +
			f'((unsigned int) { cbits })')
	print(f'#define  { vprefix }_VARBITS_NET     ' +
			f'((unsigned int) { cbits-2 })')
## TODO: pick proper bit from above
	print(f'#define  { vprefix }_ELEMS           ' +
			f'((unsigned int) { ccnt })')
	print("/**/")

	print(f'static const {ctype} { vprefix }[{ ccnt }] = {{')

	binary = ''
	for ci, c in enumerate(ct):
		cbin = ",".join(f"{cf}"  for cf in c)  +","
		print(cbin)
		binary += (' '  if ci  else '') +cbin

		if ci == 0:
			print(f'// nr.inputs={nrvars}, +{addvars} var, '+
				f'{nrcls} clauses, <={maxv} vars per clause')
			print('// /header')

	print('} ;')
	print(f'// /*flat*/ { ctype } { vprefix }[{ ccnt }] = {{ { binary } }};')

				## raw clauses: flattened original int list
				## let user figure out input/added mappings
	ix = ''
				## header: was extracted to ct[0]
				## no other component present
	assert(len(ct[0]) == vTEMPLATE_HDR_ENTRIES)
	hdrint = [ int(v, 16)  for v in ct[0] ]

	ix += (','.join(str(h)  for h in hdrint)) + ','

	for ci, c in enumerate(cls):
		ix += ' ' + (','.join(str(cf)  for cf in c))
		ix += ',0,'

	print(f'// /*ints*/ { vprefix }_INTS[{ ccnt }] = {{ { ix } }};')

	print(f'// /CLAUSES[{ len(cls) }]')

				## entries to include to template's struct
				## see sat.c
				##
	tentry = [
		f'#define  { vprefix }_FULL \\',
		f'{{ { nrvars }, \\',
		f'  { vprefix }_VARBITS,      \\',
		f'  { vprefix }_MASK,         \\',
		f'  { vprefix }_IS_NEGATIVE,  \\',
		f'  { vprefix }_IS_ADDED_VAR, \\',
		f'  { vprefix }_INPUT_VARS,   \\',
		f'  { vprefix }_ADDL_VARS,    \\',
		f'  { vprefix }_CLAUSES,      \\',
		f'  { vprefix }_MAX_CLS_VARS, \\',
		f'  (const void *)            \\',
		f'      { vprefix },          \\',
		f'  { vprefix }_ELEMS,        \\',
		'}',
	]
	##
	print('\n'.join(tentry))

	print('// /GENERATED.SRC')
	print('// }')
	print()


##--------------------------------------
## 'units' turn variable indexes (<0, >0) into unsigned ints in template-table
##   - special-casing negated ones (MS bit)
##   - marking added-variable indexes
##   - marking end-of-clause indexes
##
def varidx2mem(idx, nrvars, unitbits):
	negbit, addvbit = markbits(unitbits)

	if abs(idx) <= nrvars:
		c = abs(idx)
	else:                   ## index is additional variable
	                        ## marked+rebased to 0: 3 vars, 5 -> addv | 2
		c = abs(idx) - nrvars

		if (addvbit <= c):
			raise ValueError("inconsistent unitbits+var.index")

		c |= addvbit

	c |= negbit  if (idx < 0)  else 0

	return c


##--------------------------------------
## given clauses, input (V) plus added intermediate (A) variables, turn clause
## list into template:
##   (1) symbolic templates
##     (1) input variables are numbered 1..V
##     (2) intermediate variables are numbered V+1..V+A
##   (2) numeric templates  <->  'vars' and 'nvars' are integers
##     -> only numeric expressions
##
## see templ2c() for cases where template has already been fully
## processed
##
## 'result' MUST be one of variables if not ''; if it is an intermediate one,
## it will be assigned index V+1
##   - if True or False, results are forced and not assigned to a variable
## TODO: multi-valued variant, where this is a list
##
## returns [ [ clauses1 ], [ clauses2 ], ... ], total elem.count,
##           nr. of clauses, nr. added variables (A), max.variables
##           (worst-case clause), unit.bitcount
##
## TODO: return proper dict/struct
##
## elem.count includes 0-padding, PLUS HEADER:
##     (1) nr. of input variables (V)
##     (2) nr. of added/intermediate variables (A)
##     (3) nr. of clauses
##     (4) max nr. of variables in worst-case clause (excluding terminating 0)
## see vTEMPLATE_HDR_ENTRIES
##
## all values padded to uniform width which accommodates MAX(V,A) plus two bits
##     x8...  ->  index is negated (<0)
##     x4...  ->  index of added/intermediate variable
## LS bits are actual variable index, >0
##
## compact >1  squeezes out all whitespace
##          1  adds spaces, not newlines, between clause list
##          0  one clause per line
##
## note: not taking already-populated SAT state, since it may contain
## other variables/clauses---for example: multiple instances of
## functions of the same varaible. we construct exact list of of
## additional variables not in 'vars'
##
def clauses2params(cls, vars, nvars, result, raw=True, unitbits=0):
	sv  = set(vars)
	snv = set(nvars)

	if len(sv) != len(vars):
		raise ValueError("non-unique input list")
	if len(snv) != len(nvars):
		raise ValueError("non-unique added-variable list")

## TODO: union, check size vs. union(vars+nvars)

	s = satsolv_init0()

	satsolv_add_vars(s, vars)
		##
##	for nv in nvars:
##		satsolv_add_1var(s, nv)

	if ((result != '') and (result != []) and (result != True) and
	    (result != False)):
		satsolv_add_vars(s, [ result ])         ## NOP if one of inputs

	if raw:
		addvars = list(a  for a in satsolv_clauses2ids(cls)
			       if (not a in vars))
	else:
		addvars = list(range(len(vars), len(vars)+len(nvars)))

	satsolv_register_added_vars(s, len(addvars))

	satsolv_add_vars(s, list(a  for a in addvars  if (a != result)))
					## ID-to-index lookup, 1..V, V+1..V+A

					## nr. of bits(integers) +sign(1)
					## +is-added-variable?(1)
					##
	intbits = len(s[ 'vars' ]).bit_length() +vTEMPLATE_ADDL_BITS
					##
					## ideally, this is exactly V+A
					## in other words, >= MAX(V, A)
					##
	if unitbits and (unitbits < intbits):
		raise ValueError("invalid minimum-template width")

	intbits = ((intbits +7) //8) *8                    ## pad to full bytes
	intbits = max(unitbits, intbits)

	intxdigits = ((intbits //8) * 2)

	res, maxcvars = [], 0

			## constants to mark variables, aligned to MS(intbits)
			##   0x8...  variable is negated (<0)
			##   0x4...  last variable of clause
			##   0x2...  added/intermediate, not input variable
			##
	neg   = 1 << (intbits -1)
	added = 1 << (intbits -2)
	fmt0  = f'0x{ 0 :0{intxdigits}x}'

	for c in cls:
## TODO: recurring, factor out all 'if raw...' paths
		if raw:
			signs, ids = satsolv_str2ids(c.split())
						## keep ints >0
						## append sign separately
			ints = list(satsolv_vars2ints(s, [ i ])[0]
				    for i in ids)
		else:
			ids   = list(abs(v)  for v in c)
			ints  = ids[:]
			signs = list(('-'  if (v<0) else '')  for v in c)

						## keep ints >0
						## append sign separately
		res.append([])

						## pretty-print
		pprint = (f"{ sig }{ id }[{ i }]"  for sig, id, i
		          in zip(signs, ids, ints))

		print('//', " ".join(pprint))

				## signs, ids, ints of uniform element count
				## ('-' or ''); name; variable index>0

		for zi, zv in enumerate(zip(signs, ids, ints)):
			sig, id, i = zv

				## set extra bits
				##
			r = 0  if (sig == '')  else neg

## TODO: track variable type, turn into base-index

			if (i > len(vars)):          ## added variable ->
			                             ## rebase to 1..A
				i -= len(vars)       ## ADDED(0) -> absolute 1
				r |= added

				## MS bits MUST NOT conflict with index
			r = f'0x{ r+i :0{intxdigits}x}'

			res[-1].append(r)

		maxcvars = max(maxcvars, len(ids))
		res[-1].append(fmt0)

	print(f'// /CLAUSES[{ len(cls) }]')

				## do not expect this with sane data:
				## _lots_ of clauses with few variables
				##
	if (maxcvars > neg):
		raise ValueError("nr. of clauses does not fit bitwidth")

		## lead/header: total nr. of entries, nr. of inputs
		##
	res.insert(0, [ f'0x{ len(vars)    :0{intxdigits}x}',
	                f'0x{ len(addvars) :0{intxdigits}x}',
	                f'0x{ len(cls)     :0{intxdigits}x}',
	                f'0x{ maxcvars     :0{intxdigits}x}', ])
## TODO: use template2hdr()
		##
		## appends vTEMPLATE_HDR_ENTRIES elems

	units = sum(len(r)  for r in res)

	return res, units, len(cls), len(res), len(addvars), maxcvars, intbits


##--------------------------------------
def print_ctemplate_hdr(ctypebits):
	print('//')
	print('// { ///')    ## leave trailing '///'
	                     ## it is a 'do not count indentation' marker
	                     ## for our reformatters
	print('// GENERATED.SRC:')

	print(f"#if !defined({ sCNF_TEMPLHDR_ID })")
	print("/* first elements storing input/additional-var count (2),")
	print(" * nr. of clauses(1), and max-nr-of-variables per clause (+1)")
	print(" */")
		##
	print(f"#define { sCNF_TEMPLHDR_ID } " +
		f"((unsigned int) { vTEMPLATE_HDR_ENTRIES })")
	print("#endif")
	print("/**/")

	return ctype(ctypebits)


##--------------------------------------
def uconst(bits):
	return f'UINT{ bits }_C'


##--------------------------------------
## return C conditional-define wrappers:
##   #if !defined(...)
##   #define ...
##   #endif wrappers
##
def cond_define(var, value, terminator='//'):
	res = [
		f'#if !defined({ var })',
		f'#define  { var }  { value }',
		'#endif',
	]

	if terminator != None:
		res.append(terminator)

	return res


##--------------------------------------
def markbits(bits):
	negd   = 1 << (bits -1)     ## variable is negated
	addvar = 1 << (bits -2)     ## additional, not input variable

	return [ negd, addvar ]


## ##--------------------------------------
## ## generate C constant table for template
## ##
## ## if 'nvars' is integer, 'cls' MUST be already a Template; we
## ## only use number of variables
## ## (see 'Symbolic template' for struct)
## ##
## ## 'r' is name of output Boolean, which will be assigned as 1st add'l variable
## ## if True or False, results are forced and not assigned to a variable
## ##
## ## 'tid' is template ID, string to include in C definitions
## ##
## ## TODO: multi-valued output MUST accommodate list
## ##
## def clauses2print(cls, vars, nvars, r, tid):
## 	ct, ccnt, nrcls, units, addvars, maxv, cbits = clauses2params(cls,
## 	                                                vars, nvars, result=r)
## 	nrvars = len(vars)
##
## 	if len(ct[0]) != vTEMPLATE_HDR_ENTRIES:
## 		raise("first clause->template does not look like header")
##
## 	ctype = print_ctemplate_hdr(cbits)
##
## 					## full listing, one clause per line
##
## 	print(f'// CLAUSES[TYPE={ ctype }]' +
## 		f'[{ nrvars }+{ addvars }(x{ nrvars :x}+' +
## 		f'x{ addvars :x})({ nrvars +addvars }/' +
## 		f'x{ nrvars +addvars :x}) variables]' +
## 		f'x[max { maxv } vars/cls]:')
##
## 	negbit, _, addvbit = markbits(unitbits)
## 	maskbits = min(negbit, clsendb, addvbit) -1
##
##
## ## TODO: sync clause-to-print etc. heuristics
##
## 				## bit width, masking macros
## 	print("/**/")
## 	print(f'#define  SAT_TEMP_L{ tid }{ len(vars) }_MASK         ' +
## 			f'UINT{ cbits }_C(0x{ (1 << (cbits -2)) -1 :x})')
## 		##
## 	print(f'#define  SAT_TEMP_L{ tid }{ len(vars) }_IS_NEGATIVE  ' +
## 			f'UINT{ cbits }_C(0x{ 1 << (cbits -1) :x})')
## 		##
## 	print(f'#define  SAT_TEMP_L{ tid }{ len(vars) }_IS_CLAUSE_END ' +
## 			f'UINT{ cbits }_C(0x{ 1 << (cbits -2) :x})')
## 		##
## 	print(f'#define  SAT_TEMP_L{ tid }{ len(vars) }_IS_ADDED_VAR ' +
## 			f'UINT{ cbits }_C(0x{ 1 << (cbits -3) :x})')
## 	print("/**/")
##
## 	print(f'#define  SAT_TEMP_L{ tid }{ nrvars }_INPUT_VARS   ' +
## 			f'((unsigned int) { nrvars })')
## 	print(f'#define  SAT_TEMP_L{ tid }{ nrvars }_ADDL_VARS    ' +
## 			f'((unsigned int) { addvars })')
## 	print(f'#define  SAT_TEMP_L{ tid }{ nrvars }_CLAUSES      ' +
## 			f'((unsigned int) { nrcls })')
## 	print(f'#define  SAT_TEMP_L{ tid }{ nrvars }_MAX_CLS_VARS ' +
## 			f'((unsigned int) { maxv  })')
## 	print(f'#define  SAT_TEMP_L{ tid }{ nrvars }_VARBITS      ' +
## 			f'((unsigned int) { cbits })')
## 	print(f'#define  SAT_TEMP_L{ tid }{ nrvars }_ELEMS        ' +
## 			f'((unsigned int) { ccnt })')
## 	print("/**/")
## 	print(f'static const {ctype} SAT_TEMP_L{ tid }{ nrvars }' +
## 		f'[{ ccnt }] = {{')
##
## 	for ci, c in enumerate(ct):
## 		print(",".join(f"{cf}"  for cf in c)  +",")
##
## 		if ci == 0:
## 			print('// /header')
## 			print('//')
##
## 	print('} ;')
## 	print('// /CLAUSES')
##
## 				## entries to include to template's struct
## 				## see sat.c
## 				##
## 	tentry = [
## 		f'#define  SAT_TEMPL_{ tid }{ nrvars }_FULL \\',
## 		f'{{ { nrvars }, \\',
## 		f'  SAT_TEMPL_{ tid }{ nrvars }_VARBITS,      \\',
## 		f'  SAT_TEMPL_{ tid }{ nrvars }_MASK,         \\',
## 		f'  SAT_TEMPL_{ tid }{ nrvars }_IS_NEGATIVE,  \\',
## 		f'  SAT_TEMPL_{ tid }{ nrvars }_IS_ADDED_VAR, \\',
## 		f'  SAT_TEMPL_{ tid }{ nrvars }_INPUT_VARS,   \\',
## 		f'  SAT_TEMPL_{ tid }{ nrvars }_ADDL_VARS,    \\',
## 		f'  SAT_TEMPL_{ tid }{ nrvars }_CLAUSES,      \\',
## 		f'  SAT_TEMPL_{ tid }{ nrvars }_MAX_CLS_VARS, \\',
## 		f'  SAT_TEMPL_{ tid }{ nrvars }_CLSVARS_USED, \\',
## 		f'  (const void *)                           \\',
## 		f'      SAT_TEMPL_{ tid }{ nrvars },          \\',
## 		f'  SAT_TEMPL_{ tid }{ nrvars }_ELEMS,        \\',
## 		'}',
## 	]
## 	##
## 	print('\n'.join(tentry))
##
## 	print('// /GENERATED.SRC')
## 	print('// }')
## 	print()


##--------------------------------------
## 'intbits' 0  parses template, and returns parameters as 'Template summary'
## 'intbits' >0 generates C template, forcing to list of
##              lists, each with fixed width 0x...elems... entries
##              - first entry is header if requested
##              - clauses follow
##
## only non-symbolic templates
##
def template2c(t, header=True, intbits=0):
	nrvars   = t[ 'inputs'   ]
	nraddl   = t[ 'add.vars' ]
	cls      = t[ 'clauses'  ]
	if not cls:
		return
	maxvars  = max(len(c)  for c in cls)

					## ...clauses1... <terminating 0>
					## ...clauses2... <terminating 0>
					## ...
					##
	units  = sum(len(c)  for c in cls) + len(cls)
	units += (vTEMPLATE_HDR_ENTRIES  if header  else 1)
					## header does not add 0-terminator

	unitbits = (nrvars + nraddl).bit_length() +vTEMPLATE_ADDL_BITS

	if intbits == 0:
		return { 'units': units, 'unit.bits': unitbits }

	if (intbits < unitbits):
		raise ValueError("inconsistent int/unit bits")
	unitbits = intbits

	res = []
	if header:
		res.append(template2hdr(t, fmtbits=intbits))

			## [[1, 2, -3], [-1, 2, 3], [1, -2, 3], [-1, -2, -3]]
			##
	for c in t[ 'clauses' ]:
		maxv = max(abs(v) for v in c)
		if maxv > nrvars + nraddl:
			raise ValueError('clause out of range in "{t}"')
## TODO: use centralized clause-verify macros

		cmem = []
		for ce in c:
			cmem.extend([ varidx2mem(ce, nrvars, unitbits) ])
		cmem.append(vCLAUSE_TERMINATOR)

		res.append( ints2xbits(cmem, unitbits) )

	return res


##--------------------------------------
## given an array of templates, construct a single C struct from them
##
## 'condense' selects between array-of-identical-structs or collapsed table
##
## TODO: we have a standalone bin2table.py; simplify to pretty-print
## single template, and let bin-to-table convert+pack everything
##
def templates2c(templs, tid, condense=True, unitbits=0):
	units, maxubits = [], -1
	for t in templs:
		ts = template2c(t, header=True, intbits=0)

		units.append(ts[ 'units' ])
		maxubits = max(maxubits, ts[ 'unit.bits' ])

## TODO: use centralized macro for round-to-uint-sizes
	if 'MAXBITS' in os.environ:
		mxb = int(os.environ[ 'MAXBITS' ], 0)         ## TODO: +checker
		if 8 * ((maxubits +1) // 8) > mxb:
			raise ValueError("unit size out of range")

	if maxubits >= 17:
		maxubits = 32
	elif maxubits >= 9:
		maxubits = 16
	else:
		maxubits = 8

	maxubits = max(maxubits, unitbits)
	utype    = ctype(maxubits)

	if condense:		## collapse all entries into single list
				## no padding needed, since clause lists use
				## in-band terminator markers
		ctext = []
		elems = []      ## collect (start index, nr. of entries) pairs

		maxvars    = -1
		maxaddvars = -1
		maxcvars   = -1 ## max. nr. of variables per clause
		maxclauses = -1

		elems = [ [ 0, vFULLTEMPLATE_HDR_ENTRIES ] ]

		for t in templs:
			cls = template2c(t, header=True, intbits=maxubits)

			maxclauses = max(maxclauses, len(t['clauses']))
			maxvars    = max(maxvars,    (t[ 'inputs'   ]))
			maxaddvars = max(maxaddvars, (t[ 'add.vars' ]))

			cunits = 0
			for ci, c in enumerate(cls):
				ctx = ",".join(f"{var}" for var in c)

				cunits += len(c)

				if (ci == 0):
					ctext.append(f'\t{ ctx },')
					h = template2hdr(t)
					ctext[-1] += '    ' +hdr2descr(h)

## TODO: symbolic ref: [3] happens to be max.nr.vars(clause)
					maxcvars   = max(maxcvars, h[3])

				elif (ci == 1):
					ctext.append(f'\t\t{ ctx }')
				else:
					ctext[-1] += (f', { ctx }')

			ctext[-1] += (",")
##			ctext.append('')

				## nr. of preceding entries; current count
			elems.append([ elems[-1][0] +elems[-1][1], cunits ])

		elems.pop(0)    ## currently, not indexed (1-based v.count idx)

		negbit, addv = markbits(maxubits)
		maskbits = min(negbit, addv) -1

		res = []
		res.extend(cond_define('RRR_VAR_IS_NEGATED',
		                  f'{ uconst(maxubits) } (0x{ negbit :x})'))

		res.extend(cond_define('RRR_VAR_IS_ADDED',
		                 f'{ uconst(maxubits) } (0x{ addv :x})'))

		res.extend(cond_define('RRR_VAR_MASK',
		                 f'{ uconst(maxubits) } (0x{ maskbits :x})'))

		res.extend(cond_define('RRR_MAX_VARS',
		                       f'((unsigned int) { maxvars })'));

		res.extend(cond_define('RRR_MAX_ADDL_VARS',
		                       f'((unsigned int) { maxaddvars })'));

		res.extend(cond_define('RRR_MAX_CLAUSES',
		                       f'((unsigned int) { maxclauses })'));

		res.extend(cond_define('RRR_MAX_VARS_PER_CLAUSE',
		                       f'((unsigned int) { maxcvars })',
		                       terminator=''));

		res.extend([
			f'typedef { utype } RRR_Var_t;',
			'',
		])

		nrunits =  sum(elems[-1])  if elems  else 0
		nrunits += vFULLTEMPLATE_HDR_ENTRIES

		res.extend([
			f'static const { utype } RRR_templates' +
				f'[{ nrunits }] = {{',
		])

		res.extend([
			'\t' +
			(",".join(f"{var}" for var in
				ints2xbits([ maxvars, maxaddvars,
				     maxcvars, maxclauses, ], maxubits))) +",",
## TODO: expand
			'/**/',
		])

		res.extend(ctext)

		res.extend([
			'} ;',
			'',

			'/* index list, 1-based var.count to entries */',
			'static const struct TemplIndex {',
			'\tunsigned int offset;',
			'\tunsigned int count;',
			f'}} RRR_INDEX[{ len(elems) }] = {{',
				## 1-based; 0 is global counters' header
		])

## TODO: do we have a centralized align-columns() macro?

		if elems:
			maxwid1 = max(len(str(e[0])) for e in elems)
			maxwid2 = max(len(str(e[1])) for e in elems)
			##
			for e in elems:
				res.append(f'\t{{ { e[0] :>{ maxwid1 }}, ' +
					f'{ e[1] :>{ maxwid2 }} }},')
		res.extend([
			'} ;',
			'',
		])

	else:
		print(f'static const { utype } RRR[][] = {{')
		print('} ;')

	print('\n'.join(res))
#         (1) nr. of input variables (V)
#         (2) nr. of added/intermediate variables (A)
##     (3) nr. of clauses
##     (4) max nr. of variables in worst-case clause (excluding terminating 0)
	print()


##============================================================================
def template2python(t):
	sys.exit(0)


##--------------------------------------
def or_templates(mode, minn, maxn):
	fce = False  if (mode == 'OR')  else True

	print(f'[  ## OR(1..{maxn}) templates')

	for vb in range(minn, maxn+1):
		t = satsolv_or('', vb, negate=False,
		               force=fce, template=True)
		templs.append(t)
		for t in templs:
			print('\t', t, ',', sep='')
		print(']\n')
		##
		for t in templs:
			ivars = t[ 'inputs' ]
			nvars = list(range(ivars +1, ivars +1
				                      +t[ 'add.vars' ]))
			##
			clauses2print(t[ 'clauses' ], vars[ :ivars ],
			        nvars, t[ 'result'  ], 'OR',
			        raw=False)   ## , instance=str(i))
	return mode


##======================================
if __name__ == '__main__':
	sat  = satsolv_init0()
	vars = []

##	for i in range(1, 12+1):
##		v1  = list(range(1,   i+1  ))
##		v2  = list(range(i+1, i+i+1))
##		res = satsolv_diff_template(v1, v2)
##		print(f'## DIFF({i})')
##		print('xxx ', res)
##
##		nvars = list(range(i+i+1, i+i+1 +res[ 'add.vars' ]))
##
##		clauses2print(res[ 'clauses' ], vars[ : 2*i ],
##		        nvars, res[ 'result'  ], 'DIFF',
##		        raw=False, instance=str(i))
##	sys.exit(0)

	BITS     = int(os.environ['BITS'])  if 'BITS' in os.environ  else 4
	unitbits = int(os.environ['UNIT'])  if 'UNIT' in os.environ  else 0

	maxn     = 128
	vdigits  = log10(BITS)
	maxn     = 64         ## RRR

	vars = [f'v{v:0{vdigits}}'  for v in range(maxn)]

	if 'TEMPLATE' in os.environ:
		what = os.environ[ 'TEMPLATE' ].split(',')
		templs, tid = [], 'UNKNOWN'

		if 'OR' in what:
			tid = or_templates('OR', 1, maxn)

		if 'OR.FORCE' in what:
			tid = or_templates('OR.FORCE', 1, maxn)

		if 'AND' in what:
			print(f'[  ## AND(1..{maxn}) templates, 0-based index')
			for vb in range(1, maxn+1):
				t = satsolv_and('', vb, negate=False,
				                force=False, template=True)
				templs.append(t)
			for t in templs:
				ivars = t[ 'inputs' ]
				nvars = list(range(ivars +1, ivars +1
				                      +t[ 'add.vars' ]))
				##
				clauses2print(t[ 'clauses' ], vars[ :ivars ],
				        nvars, t[ 'result'  ], 'OR',
				        raw=False)   ## , instance=str(i))
## TODO: these trailers have evolved to be ~identical; factor out
			for t in templs:
				print('\t', t, ',', sep='')
			print(']\n')
			tid='AND'

		if '1OFN' in what:
			print(f'[  ## 1-of-N(1..{maxn}) templates, 0-based index')

			for vb in range(1, 64+1):    ## TODO: range(1, maxn+1):
				res = satsolv_1ofn_2prod(None, vb, allow0=False,
				                  force=True, template=True)
				print('\t', res, ',', sep='')

				if satsolv_is_debug():
					print(f'## 1-OF-N({vb})', res)

				## +1: result always has its own variable now
				nvars = list(range(vb +1, vb +1
				                      +res[ 'add.vars' ]))
				##
				clauses2print(res[ 'clauses' ], vars[ :vb ],
				        nvars, res[ 'result'  ], '1OFN',
				        raw=False, instance=str(vb),
				        unitbits=unitbits)

		if 'SUM' in what:
			print(f'[  ## SUM((1..4x M bits) templates, 0-based index')

			for emax in range(1, 4):           ## MAX(elem)
				for ne in range(1, 8):     ## NR(elems)
					t = satsolv_sum_template(ne, emax)
					print('\t', t, ',', sep='')
			print(']\n')
			tid='SUM'

		if '1OFN.VAR' in what:
			print(f'[  ## 1-of-N(1..{maxn}) templates, 0-based index')
			print(f'   ## result in variable')

			for vb in range(1, 128+1):    ## TODO: range(1, maxn+1):
				templs.append(satsolv_1ofn_2prod(None, vb,
						allow0=False, force=False,
						template=True))
			for t in templs:
				print('\t', t, ',', sep='')
			print(']\n')
			tid='1_OF_N'

					## template constructor has its own
					## pretty-printer; just dumping result
					## sufficient w/o further annotations
		if ('LT' in what) or ('LT.FORCE' in what):
			result = True  if ('LT.FORCE' in what)  else None

			for i in range(1, 4096):
				nbits = i.bit_length()
				res = satsolv_less_than_template(sat, nbits, i,
				              result=result)

				if satsolv_is_debug():
					print(f'## LT({i})', res)

				## +1: result always has its own variable now
				nvars = list(range(nbits +1, nbits +1
				                      +res[ 'add.vars' ]))
				##
				clauses2print(res[ 'clauses' ], vars[ :nbits ],
				        nvars, res[ 'result'  ], 'LT',
				        raw=False, instance=str(i))

		if 'NEQ0' in what:
			for i in range(1, BITS+1):
				res = satsolv_noneq0_template(i, force=True)

				if satsolv_is_debug():
					print(f'## NEQ-OR0({i})', res)
## TODO: recurring feature 'list all added variables'
				nvars = list(range(i+1, i+1+res[ 'add.vars' ]))

				clauses2print(res[ 'clauses' ], vars[ : 2*i ],
				        nvars, res[ 'result'  ], 'NEQ0',
				        raw=False, instance=str(i))

## both OR(...vars1...) and OR(...vars2...) are known
## param order:
##    ...vars1...  ...vars2...  OR1(..vars1..)  OR2(..vars2..)
## forced output, so no ret.value
##
		if 'NEQ0.OR.FORCE' in what:
			for i in range(1, BITS+1):
				or1, or2 = i+i+1, i+i+2

				res = satsolv_noneq0_template(i, force=True,
				              or1=or1, or2=or2)

				if satsolv_is_debug():
					print(f'## NEQ-OR0-FORCE.OR({i}+2)', res)
## TODO: recurring feature 'list all added variables'
				nvars = list(range(i+1, i+1+res[ 'add.vars' ]))

				clauses2print(res[ 'clauses' ], vars[ : 2*i ],
				        nvars, res[ 'result'  ], 'NEQ0',
				        raw=False, instance=str(i))

		if 'DIFF' in what:
			for i in range(1, BITS+1):
				v1 = range(1,     i+1)
				v2 = range(i+1, 2*i+1)
				res = satsolv_diff_template(v1, v2)

				if satsolv_is_debug():
					print(f'## DIFF({i})', res)
## TODO: recurring feature 'list all added variables'
				nvars = list(range(i+1, i+1+res[ 'add.vars' ]))

				clauses2print(res[ 'clauses' ], vars[ : 2*i ],
				        nvars, res[ 'result'  ], 'DIFF',
				        raw=False, instance=str(i))

		if 'C' in what:
			templates2c(templs, tid=tid)

		sys.exit(0)
		##-------------------------------

		if os.environ[ 'TEMPLATE' ] == '1OFN':
			r, nvars, cls, comm = satsolv_1ofn_2prod(sat,
			                                   vars[ :BITS ])
		print(f'## 1-of-N[{ BITS }] r={r} cls[{len(cls)}]',
		      nvars, comm)

		clauses2print(cls, vars[ :BITS ], nvars, r, '1OFN')

		sys.exit(0)

	##----- 1-of-N, 1..65  ------------------

	for vb in range(1, 65):
		sat  = satsolv_init0()

		satsolv_add_vars(sat, vars[:vb])

		r, nvars, cls, comm = satsolv_1ofn_2prod(sat, vars[:vb])
		print(f'## 1-of-N[{ vb }] r={r} cls[{len(cls)}]={ cls }',
		      nvars, comm)

		sat_report_vars(sat, prefix='//')

		clauses2print(cls, vars[:vb], nvars, r, '1OFN')

		if vb < 4:
			r, nvars, cls, comm = satsolv_1ofn_2prod(sat,
			                              vars[:vb], allow0=True)
			print(f'## 0/1-of-N[{ vb }] r={r} cls[{len(cls)}]',
			      nvars, comm)
			print()

	sys.exit(0)  ##--------------------------


	##----- 1-of-N --------------------------
	vars.extend([f'v{v:0{vdigits}}'  for v in range(BITS)])

	res = 'R'

	satsolv_add_vars(sat, vars)
	satsolv_add_vars(sat, [ res ])

	satsolv_1ofn(sat, vars, result=res)
	satsolv_report(sat)
	sys.exit(0)  ##--------------------------

	if 'NONEQ0' in os.environ:
		satsolv_noneq0_template(BITS)

	res  = 'NEQ'

	for ext in range(2):
		for v in range(BITS):
			vars.append(f'v{ext}_{v:0{vdigits}}')

	satsolv_add_vars(sat, vars)
	satsolv_add_vars(sat, [ res ])
		##
		## register <inputs bits | result(bit)> as first variables
		## allows checking truth table for these, since only
		## intermediate vars follow

	cls, neq, comm = satsolv_neq_or0(sat, vars[:BITS], vars[ BITS : BITS*2 ],
	                                 result=res)
	for c in cls:
		satsolv_add_constraint1(sat, sSAT_SYM_PREFIX +c, comm)
		comm = ''

	satsolv_report(sat)
	sys.exit(0)

	for i in range(len(vars) // BITS):
		r = f'OR{ len(sat["vars"]) }'
		satsolv_add_1var(sat, r)

		ivars = vars[ i*BITS:i*BITS+BITS ]

		orx, _, _ = satsolv_or('', ivars, result=r)
		for c in orx:
			satsolv_add_constraint1(sat, sSAT_SYM_PREFIX +c)

		satsolv_add_constraint1(sat, sSAT_SYM_PREFIX +'{r} 0')

		for j in range(i+1, len(vars) // BITS):
			if i == j:
				continue

			cls, neq, comm = satsolv_neq_or0(sat, ivars,
				vars[ j*BITS:j*BITS+BITS ])
			for c in cls:
				satsolv_add_constraint1(sat,
					sSAT_SYM_PREFIX +c, comm)
				comm = ''

			satsolv_add_constraint1(sat, sSAT_SYM_PREFIX +'{neq} 0')

	satsolv_report(sat)
	sys.exit(0)

	if False:
		cmp_truthtable(2)
		cmp_truthtable(3)
		cmp_truthtable(4)
		cmp_truthtable(5)
		cmp_truthtable(6)
		sys.exit(0)

	satsolv_add_vars(sat, vars)

#	maxv = 4
#	res  = satsolv_less_than(sat, vars, 4)
#	print('<4', res)
#	res  = satsolv_less_than(sat, vars, 5)
#	print('<5', res)
#	res  = satsolv_less_than(sat, vars, 6)
#	print('<6', res)
#	res  = satsolv_less_than(sat, vars, (1 << len(vars)) -1)
#	print('<full', res)

	v2 = [ 'vA', 'vB', 'vC', ]

	satsolv_add_vars(sat, v2)

	satsolv_neq_or0(sat, vars, v2)
	satsolv_report(sat)

