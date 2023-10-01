#!/usr/bin/python3

# generate SAT expressions for pack/solver
#
# 'template' option outputs a compressed template, a list of variable IDs,
# a structure which lists 'virtual' register numbers which one can then
# map onto actual SAT variables. See 'Template representation' below.
#
# test modes
#   NONEQ0[=bits:combinations]   generate non-equal-or-any-0 tests
#
# Author: Visegrady, Tamas  <tamas@visegrady.ch>


sSATPREFIX  = 'SAT='      ## common prefix for data applicable to SAT solvers
sSATCOMMENT = '## SAT='   ## SAT-related comment, for our own tracing
sSAT_CONSTR_END = ' 0'    ## terminate [term list of] constraint
sSAT_2ND_VAR    = 'NV'    ## prefix for secondary SAT (CNF) variables
sSAT_SYM_PREFIX = 'RAW='  ## prefix for clauses which are stored as strings,
                          ## only mapped to integer indexes in the end
                          ## DIMACS CNF: "1 2 -3 0"
                          ## 'raw' CNF:  "D1 D2 -D3"

import os, textwrap, sys, math, itertools, re

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


##--------------------------------------
def allpairs(vars):
	return itertools.combinations(vars, 2)


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
##   }
##
## Numeric template:
##   { 'descr':    ...comment...
##     'inputs':   [ ...list of input variable indexes... ],     ## N entries
##     'add.vars': M,                 ## number of new variables
##     'clauses': [
##       [ clause1... ]
##       [ clause2... ]
##       ...
##                   ## clauses may use -N-M .. -1, 1 .. N+M
##                   ## no other variable indexes MAY be referenced
##     ]
##   }
##
## in both forms, assume [1 .. N] are original inputs; [N+1 .. N+M] are
## implicit added variables
##
## 'in.base' and 'add.base', when >0, indicate template has been
## rebased: input and additional-variable index starts at >0
##
## clauses' ordering conveys some idea about any hierarchical
## problem decomposition; there is no real implied order.


##--------------------------------------
## empty construct for SAT solver aux. data
##
def template0(descr='UNDEFINED', inputs=0, in_base=0):
	return {
		'descr':     descr,
		'inputs':    inputs,
		'add.vars':  0,
		'in.base':   in_base,
		'add.base':  0,
		'clauses':   [],
		'comments':  [],
	}


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
## input is list of text IDs
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
		for id in satsolv_str2ids(c.split())[1]:
			if not id in r:
				r.append(id)

			## str2ids returns (sign, sign2) (id1, id2) etc.
			## pass through only id1/2 etc.

	return r


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
## polymorphic negation
##   - integers: swap sign; 0 is invalid input
##   - strings/symbolic names: add or remove leading '-'
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
def satsolv_xor1_template(var1, var2, negate=False, force=False):
	res  = template0('XNOR(2)'  if negate  else 'XOR(2)', inputs=2)
	##
	res[ 'add.vars' ] = 1

	rv = -3  if negate  else 3

	res[ 'clauses' ] = [             ## truth table for "{var1} XOR {var2}"
		[         var1,          var2,  sat_not(rv), ],
		[ sat_not(var1),         var2,          rv,  ],
		[         var1,  sat_not(var2),         rv,  ],
		[ sat_not(var1), sat_not(var2), sat_not(rv), ],
	]

	if force:
		res[ 'clauses' ].append([ rv ])

	return res


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
def satsolv_or2(var1, var2, result, negate=False, template=False):
						## negate: sign for -R/R

## TODO: obsoleted if split properly -> separate ''/- fields
	rsign1, rsign2 = ('', '-')  if negate  else ('-', '')
		## sign(R) in all-enclosing (1) and per-variable (2) lines

	if template:
## TODO: numeric only; add symbolic form
## TODO: use template0() calls and remove standalone pieces
		return {
			'inputs':   2,
			'add.vars': 1,
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
def satsolv_and_template(vars, negate=False, force=False):
	vars = vars2varlist(vars)
	res  = template0('AND', inputs=len(vars))

	if isinstance(vars[0], int):               ## numeric list, 'vars' == N
		val2set = []           ## set to [ variable, value ] if forced

		if len(vars) == 1:
			if force:                ## OR(1) -> force one variable
				res[ 'descr' ] += '(1)->force'
				val2set = [ vars[0], not negate ]

			else:          ## NOP: single variable, arbitrary state
				res[ 'descr' ] += '(1)->NOP'
		else:
			res[ 'descr'    ] += f'({ len(vars) })'
			res[ 'add.vars' ] = 1

				## 1) not(A) | not(B) | R   (A & B) -> R
				## 2) A | not(R)            not(A) -> not(R);...
				## 3) B | not(R)

## TODO: changes w/ symbolic form
			rv = -len(vars)-1  if negate  else len(vars)+1

			res[ 'clauses' ] = [ [ sat_not(v)  for v in vars ] ]
			res[ 'clauses' ][-1].append(rv)

			nrv = sat_not(rv)

			res[ 'clauses' ].extend(
				[ [ v, nrv ]  for v in vars ]
			)

			if force:
				val2set = [ len(vars) +1, not negate ]

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
def satsolv_or_template(vars, negate=False, force=False):
	vars = vars2varlist(vars)
	res  = template0('OR', inputs=len(vars))

	if isinstance(vars[0], int):               ## numeric list, 'vars' == N
		val2set = []           ## set to [ variable, value ] if forced

		if len(vars) == 1:
			if force:                ## OR(1) -> force one variable
				res[ 'descr' ] = f'OR(1)->force'
				val2set = [ vars[0], not negate ]

			else:          ## NOP: single variable, arbitrary state
				res[ 'descr' ] = f'OR(1)->NOP'
		else:
			res[ 'descr'    ] = f'OR({ len(vars) })'
			res[ 'add.vars' ] = 1

				## 1) A | B | not(R)  not(A) & not(B) -> not(R)
				## 2) not(A) | R      A -> R; B -> R  ...
				## 3) not(B) | R

			rv = -len(vars)-1  if negate  else len(vars)+1

			res[ 'clauses' ] = [ vars[:] ]
			res[ 'clauses' ][-1].append(-rv)

			res[ 'clauses' ].extend(
				[ [ -v, rv ]  for v in vars ]
			)

			if force:
				val2set = [ len(vars) +1, not negate ]

		if val2set:
			res[ 'clauses' ].append(
				clause2set(val2set[0], val2set[1], force=force)
			)

		return res

	assert(0)


##-----------------------------------------
## numeric templates assume 1..V base variables and V+1..V+A additional ones
## shift template for base to start at 'vars' and additional ones
## at 'addl_vars'
##
## NOP, checking only 't' with 'vars' and 'addl_vars' both 0
## TODO: currently, we do not rebase repeatedly
##
def template_rebase(t, vars=0, addl_vars=0):
	ni, na = t[ 'inputs' ],  t[ 'add.vars' ]
	bi, ba = t[ 'in.base' ], t[ 'add.base' ]

	if min(ti, ta) < 0:
		raise ValueError('invalid template-variable count')

	if max(bi, ba) > 0:
		raise ValueError('template already rebased')

	res = {
		'descr':    t[' descr '],
		'inputs':   ni,
		'add.vars': na,
		'in.base':  bi +vars,
		'add.base': ba +addl_vars,
	}
	cls = []

	shift = vars +addl_vars

	for c in t[ 'clauses' ]:
		oorange = [ i  for i in c  if (abs(i) > ti+ta+ni+na) ]
		if bi+ba:
			oorange.extend(i  for i in c  if (abs(c) < ni+na))

		if oorange != []:
			raise ValueError(f'invalid template-var index ({c})')

		cls.append([ i +shift  if (i>0)  else i -shift ])

	res[ 'clauses' ] = cls

	return res


##-----------------------------------------
## predefined templates for small-N "0/1-of-N" expressions
##
## see satsolv_1n_few(), which shares logic
##
def satsolv_1ofn_2prod_few_template(vars, allow0=False, force=False):
	res, r = [], template0(('0/1'  if allow0  else '1') +
	                       f'-of-N({ len(vars) })')
	r[ 'inputs' ] = len(vars)

## TODO: clean up res/r/sub-object assignments
## TODO: does _and_template() etc. already contain small-N templates?

	if len(vars) == 1:                ## 0/1: anything; 1: var must be True
		r[ 'descr'] += ('->NOP'  if allow0  else  '->force')
		if not allow0:
			r[ 'clauses' ] = [ [ vars[0] ] ]
		return r

	elif len(vars) == 2:                        ## 1-of-A/B  or  0/1-of-A/B
		rd = r[ 'descr' ] + ('->NAND'  if allow0  else  '->XOR')
		if allow0:                     ## reject simultaneous True only
			res = satsolv_and_template(vars, negate=True)
			assert(0)
		else:
			res = satsolv_xor1_template(vars[0], vars[1],
			                            force=force)
		res[ 'descr' ] = rd
		return res

	elif len(vars) <= 4:
				## no pair of variables is simultaneously true
		r[ 'descr' ] += f'==NO.PAIRS'
		r[ 'clauses' ] = [
			[ sat_not(v1), sat_not(v2), ]
				for v1, v2  in allpairs(vars)
		]

		if not allow0:
			r1 = satsolv_or_template(vars, force=force)
			##
			r[ 'add.vars' ] += r1[ 'add.vars' ]
			r[ 'clauses'  ].extend(r1[ 'clauses' ])
			##
			## inputs are shared: no clause/index to rebase

		return r

	return None

	return res


##-----------------------------------------
## 0/1-of-N template
##
## see satsolv_1ofn_2prod(): shares much of the same logic
##
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

		p, q = matrix2pq(vars)
		comm = f'{ rstr }({ len(vars) }->{ p }x{ q })'

					## adds P+Q axis variables,
					## w/o any subsequent expressions' vars
		pvar = list(range(p))
		qvar = list(range(p, q+p))
		##
		pt = satsolv_1ofn_2prod_template(p)
		qt = satsolv_1ofn_2prod_template(q)
		##
		comm += f',({ pt[ "descr" ] })'
		comm += f'x({ qt[ "descr" ] })'

		print('xxx//', comm)
		print('xxx.p.var', pvar)
		print('xxx.q.var', qvar)
		print('xxx.pt', pt)
		print('xxx.qt', qt)
		print('##')
## RRR
		r[ 'add.vars' ] += len(pvar) +len(qvar)
		r[ 'add.vars' ] += +pt[ 'add.vars' ] + qt[ 'add.vars' ]

		return r

## TODO: symbolic mapping
	assert(0)


##-----------------------------------------
## sample: A; B; ...; R = A | B | ...
##     1) A | B | not(R)      not(A) & not(B) -> not(R)
##     2) not(A) | R          A -> R; B -> R  ...
##     3) not(B) | R
##        ...
##
## NOR with 'negate' (negates R in all clauses)
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

	all.append(f"{ rsign1 }{ result }")
		##
	cls.append( " ".join(all) )                   ## A | B | not(N)

	terms = list((base +b)  for b in v)

	cls.extend((f'-{ t } { rsign2 }{ result }')  for t in terms)

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
	8: [ 2, 4, ],       ## less levels than 3x3 decomposition?
	9: [ 3, 3, ],
}


##-----------------------------------------
## 1-of-N or 0-of-N, hierarchical decomposition: pick P+Q matrix sizes
## returns p, q per-axis sizes
##
def matrix2pq(vars):
			## assume ~square P*Q is optimal
			## TODO: minimize (cost(P) + cost(Q)) -> select P, Q
			##
	if len(vars) in tMATRIX2PQ:
		return tMATRIX2PQ[ len(vars) ]

	p = int(math.sqrt(len(vars)))
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
## of V<...constant... comparisons
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
## satsolv_less_than_2x()
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

	print()
	for rbits, r in res:
		print(rbits + '.' +('1'  if r  else '0'))
	print()


##----------------------------------------------------------------------------
## expressions compare up to two runs' worth of bits, comparing only
## bits of the most significant runs against the big-endian bit array 'vars'
##
## first run always from an all-1 region
##
## assume V is the variable's value, the three cases below compare:
##    V  <  1  0000..000
##    V  <  1111..111                         all-ones
##    V  <  111..11   000..00
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
## 'runs' in the above cases: [ [1],        [0,0,...0,0]   ]
##                            [ [1,1,1,...,1]              ]
##                            [ [1,1,..,1], [0,0,0,...0,0] ]
## 'nbits' is the printable-collapsed form, 100..00, 111..111 etc., of
## the constant which is being compared against
## 'vars' are the variables which form the comparison value
##
## returns None, None, None  if no more runs
## registers any intermediate variables
##
def satsolv_less_than_2x(sat, vars, runs, nbits):
	if runs == []:
		return None, None, None

	if runs[0][0] != 1:
		raise ValueError("bits<N did not start with all-1 bit run")

	if len(runs) > 2:
		raise ValueError("too many runs in bits<N construction")

## TODO: this special-casing of single bits disappears, once _nand_n()
## centralizes all <3 special-cased cases: can pass 1-bit comparison
## through as-is

	vdescr = 'VARS:' +(".".join(vars))

	if len(vars) < len(runs[:2]):
		raise ValueError("not enough Booleans for less-than-N-2x")

					## both 1's and 0's may be single bit
					##
					## these clauses do not need NAND/OR,
					## they can use the bit directly
					##
					## use direct1/0 for these variables,
					## if not None
					##
	direct1, direct0 = None, None

	if (len(runs[0]) == 1):                             ## single leading 1
		direct1 = vars[0]

	if (len(runs) >= 2) and (len(runs[1]) == 1):       ## single trailing 0
		direct0 = vars[ len(runs[0]) : len(runs[0]) +1 ]

	if (len(runs) == 1):                                         ## all-1's
		bits2cmp = vars[ : len(runs[0]) ]
		cls, result, xcomm = satsolv_nand_n(sat, bits2cmp)
				##
		satsolv_add_vars(sat, [ result ])
				##
		xcomm += f': ({vdescr} < { nbits }b)'

	elif (len(runs) == 2) and (len(runs[0]) == 1):
	                             ## 100..00 -> compare against a single bit

		result = vars[0]                 ## no additional condition/var
		cls    = [ f'-{result}' ]
		xcomm  = f'{result}: ({vdescr} < { nbits }b)'

	elif len(runs) <= 2:
				## 11100..000 -> NAND(...3 MS variables...)
				## 11111..111 -> NAND(...all variables...)
				##         just compare against leading 1's
				##
		bits2cmp = vars[ : len(runs[0]) ]
		cls, result, xcomm = satsolv_nand_n(sat, bits2cmp)
				##
		satsolv_add_vars(sat, [ result ])
				##
		xcomm += f': ({vdescr} < { nbits }b)'

##	elif (len(runs) == 3) and (len(runs[-1]) == 1):
##				## straightforward case:
##				##   n <= 11..100001  exactly three runs; LS one
##				##                    is a single bit
##				##
##				## construct comparison from:
##				##   (1) AND(...MS bit/s...)
##				##         -> if not, value < pattern
##				##   (2) OR(...all-0 runs' bits below...)
##				##         -> if yes, value > pattern
##				##   (3) ...comparison of LS bit...
##				##         -> if yes, value > pattern
##				##
##				## comparison is hierarchical:
##				##   (1) not-AND(1)         -> value < pattern
##				##   (2) AND(1)  AND  OR(2) -> value > pattern
##				##   (3) AND(1)  AND  NOT(OR(2))  AND
##				##          not-AND(3)      -> value < pattern
##				##
##				## with minor additions, would also extrapolate
##				## to three runs, with >1 bits in LS one: just
##				## adds a less-than-X term for the LS run
##				##
##		msvars  = vars[ : len(runs[0]) ]
##		midvars = vars[ len(runs[0]) : ]
##		lsvars  = vars[ len(runs[0])+len(runs[1]) : ]
##
##		mscls, mscmp, mscomm = satsolv_and('', msvars)
####		satsolv_add_vars(sat, [ mscmp ])
##				##   (1) -> mscmp
##
##		midcls, midcmp, midcomm = satsolv_or('', midvars)
####		satsolv_add_vars(sat, [ mscmp ])
##				##   (2) -> midcmp
##
##		lscls, lscmp, lscomm = satsolv_and('', lsvars)
####		satsolv_add_vars(sat, [ mscmp ])
##				##   (3) -> lscmp
##
##		cls, result, xcomm = None, None, None
##		print('##')

	else:
		raise ValueError("need a generic SAT/range comparison here")

	return cls, result, xcomm


##----------------------------------------------------------------------------
## are the values equal, or either one is all-0?
## forces to different-or0 with 'force'
##
## comparison for check "are A and B equal, or is at least one of them
## unassigned?" if all-0 is reserved for unassigned
##
## turns into
##    -NOR(v1) AND -NOR(v2) -> NOT-EQ(v1, v2)
##
## XXX remove the rest
##    NOR(v1) | NOR(v2) | NOT-EQ(v1, v2)
##    <->
##    NOR(v1) | NOR(v2) | OR(XOR(v1, v2))
##
## single-bit version simplifies to
##    NAND(v1, v2)     -- only the 1/1 pair is invalid
##
## returns list of clauses, result variable, comment
##
def satsolv_neq_or0(sat, v1, v2, result=None, force=False):
				## TODO: OR extra bits which are
				## in v1 or v2 only -> extra term in top clause
				## (all our current uses are identical-sized)
	if len(v1) != len(v2):
		raise ValueError("NEQ-OR0(...different sized vectors...")

	if len(v1) == 1:
		nv  = sat_new_varname2(sat, prefix='NAND')
		cmt = 'NEQ-OR0({ v1[0] } / { v2[0] }) -> NAND'
## TODO: proper piping/comment reporting
		return satsolv_nand1(x, y, result=nv)

	nor1 = sat_new_varname2(sat, prefix='NOR')
	nor2 = sat_new_varname2(sat, prefix='NOR')
		##
	cls,  _, _ = satsolv_or('', v1, negate=True, result=nor1)
	cls2, _, _ = satsolv_or('', v2, negate=True, result=nor2)
		##
	cls.extend(cls2)
				## NOR(v1), NOR(v2)

	xvars = []
				## XOR(...bits of v1..., ...bits of v2...)
				##
	for x, y in zip(v1, v2):
		xv = sat_new_varname2(sat, prefix='XOR')

		cls3, _, _ = satsolv_xor1(x, y, result=xv)
		cls.extend(cls3)
		xvars.append(xv)

				## OR(...above XOR bits...)
				## -> 1 if any XOR is 1 -> at least 1 bit diff
				## -> NOT-EQ(...)
				##
	neq = sat_new_varname2(sat, prefix='NEQ')
	cls4, _, _ = satsolv_or('', xvars, result=neq)

	cls.extend(cls4)

	if result == None:
		result = sat_new_varname2(sat, prefix='NEQ_OR0')

				## NOR(1) NOR(2) OR(XOR(...)) -> NEQ-OR0
				##
	cls5, _, _ = satsolv_or('', [ nor1, nor2, neq ], result=result)

	cls.extend(cls5)

	if force:
		cls.append(satsolv_const(result))

	cmt = f'NEQ-OR0[{ len(v1) }b]({ ",".join(v1) } / { ",".join(v2) })'

	return cls, result, cmt



##----------------------------------------------------------------------------
## is the binary combination of 'vars' < N?
## register expression to SAT variables+clauses
##
## 'vars' is bit variables, most to least significant
##
## registers any newly allocated variables to 'sat'
##
## TODO: proper binary comparison, then Quine McCluskey etc. reduction
## TODO: right now, we just pick predefined patterns
##
## since pack-n-route currently leaves only unallocated deliveries to
## the SAT solver, we expect to see not more than 3 (maybe 4)-bit variables
##
def satsolv_less_than(sat, vars, n):
	nbits = f'{ n :b}'
	nb    = list(int(b)  for b in nbits)

	if len(nbits) >= (1 << len(vars)):     ## N is wider than 2^...bits...
		return                         ## always succeeds

	runs = arr2runs(nb)

	assert(runs != [])
	assert(runs[0][0] == 1)                ## nb[] has no MS zeroes

	result, cls, xcomm = satsolv_less_than_2x(sat, vars, runs, nbits)

		## ...any special logging etc. would happen here...

	return cls, result, xcomm


##----------------------------------------------------------------------------
## filter out comment-only constraints, which do not lead to clauses
## comment-only conditions are empty strings for non-comment part
##
def sat_nr_clauses(sat):
	if (not sat) or (not "constraints" in sat):
		return 0

	nrc = sum(1  if (c[0] != '')  else  0
	          for c in sat["constraints"])

	return nrc

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
## generate many 'bits' combinations which MUST be mutually different,
## or any 0
##
## with True 'non0', we also ensure they are all non-0 (so forcing them
## to be different since all >0)
##
def many_noneq0(bits, combs=0, non0=True):
	sat     = satsolv_init0()
	vars    = []
	vdigits = log10(bits)

	if combs == 0:
		combs = (1 << bits) -1

	vars = []       ## collects tuples, each is bits of one multi-bit field

	for c in range(combs):
		nvars = []                ## added in this round

		for b in range(bits):
			nvars.append(f'v{c}_b{b:0{vdigits}}')

		satsolv_add_vars(sat, nvars)
		vars.append(nvars)

	diffs = []           ## collects difference bits; set to all>0 to force
	dvars = []           ## difference variables

				## populate pairwise-diff variables; name them
				##
	for vi in range(len(vars)):
		for vj in range(vi+1, len(vars)):
			dvars.append(f'NEQZ_{vi}_{vj}')
			satsolv_add_vars(sat, [ dvars[-1] ])
				##
				## array-of-names consumed below, in same order

	diffidx = 0
	for vi in range(len(vars)):
		for vj in range(vi+1, len(vars)):
			r = dvars[ diffidx ]
			diffidx += 1

			cls, neq, comm = satsolv_neq_or0(sat, vars[vi],
			                    vars[vj], result=r, force=True)
			for c in cls:
				satsolv_add_constraint1(sat, sSAT_SYM_PREFIX+c,
				                        comm)
				comm = ''

			diffs.append(neq)

						## force all combinations >0
	for v in vars:
		orx, r, _ = satsolv_or('', v)
		satsolv_add_vars(sat, [ r ])

		for c in orx:
			satsolv_add_constraint1(sat, sSAT_SYM_PREFIX +c)

	satsolv_report(sat)
	sys.exit(0)


##--------------------------------------
vTEMPLATE_HDR_ENTRIES = 4

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
## given clauses, input (V) plus added intermediate (A) variables, turn clause
## list into template:
##     (1) input variables are numbered 1..V
##     (2) intermediate variables are numbered V+1..V+A
##
## 'result' MUST be one of variables if not ''; if it is an intermediate one,
## it will be assigned index V+1
##     TODO: multi-valued variant, where this is a list
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
## 'array' adds C const-array frame to result
##
## note: not taking already-populated SAT state, since it may contain
## other variables/clauses---for example: multiple instances of
## functions of the same varaible. we construct exact list of of
## additional variables not in 'vars'
##
def clauses2template(cls, vars, nvars, result):
	sv, snv = set(vars), set(nvars)

	if len(sv) != len(vars):
		raise ValueError("non-unique input list")
	if len(snv) != len(nvars):
		raise ValueError("non-unique intermediate-variable list")

## TODO: union, check size vs. union(vars+nvars)

	s = satsolv_init0()

	satsolv_add_vars(s, vars)
		##
##	for nv in nvars:
##		satsolv_add_1var(s, nv)

	if (result != '') and (result != []):
		satsolv_add_vars(s, [ result ])         ## NOP if one of inputs

	addvars = list(a  for a in satsolv_clauses2ids(cls)
	               if (not a in vars))

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
	neg   = 1 << (intbits -1)
	added = 1 << (intbits -2)

	fmt0 = f'0x{ 0 :0{intxdigits}x}'

	for c in cls:
		signs, ids = satsolv_str2ids(c.split())

						## keep ints >0
						## append sign separately

		ints = list(satsolv_vars2ints(s, [ i ])[0]  for i in ids)

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

	units = sum(len(r)  for r in res)

	return res, units, len(cls), len(res), len(addvars), maxcvars, intbits


##--------------------------------------
## 'r' is name of output Boolean, which will be assigned as 1st add'l variable
## TODO: multi-valued output MUST accommodate list
##
def clauses2print(cls, vars, nvars, r):
	ct, ccnt, nrcls, units, addvars, maxv, cbits = clauses2template(cls,
	                                                vars, nvars, result=r)

	nrvars = len(vars)

	if len(ct[0]) != vTEMPLATE_HDR_ENTRIES:
		raise("first clause->template does not look like header")

	print('//')
	print('// { ///')    ## leave trailing '///'
	                     ## it is a 'do not count indentation' marker
	                     ## for our reformatters
	print('// GENERATED.SRC:')

	print(f"#if !defined({ sCNF_TEMPLHDR_ID })")
	print("/* first elements storing input/additional-var count (2)")
	print(" * and max-nr-of-variables per clause (+1)")
	print(" */")
		##
	print(f"#define { sCNF_TEMPLHDR_ID } " +
		f"((unsigned int) { vTEMPLATE_HDR_ENTRIES })")
	print("#endif")
	print("/**/")

	ctype = f'uint{ cbits }_t'

					## full listing, one clause per line

	print(f'// CLAUSES[TYPE={ ctype }]' +
		f'[{ nrvars }+{ addvars }(x{ nrvars :x}+' +
		f'x{ addvars :x})({ nrvars +addvars }/' +
		f'x{ nrvars +addvars :x}) variables]' +
		f'x[max { maxv } vars/cls]:')

	negbit   = 1 << (cbits -1)     ## negation, additional-var bits
	addvbit  = 1 << (cbits -2)
	maskbits = addvbit -1


				## bit width, masking macros
	print("/**/")
	print(f'#define  SAT_TEMPL_1_OF_N{ len(vars) }_MASK         ' +
			f'UINT{ cbits }_C(0x{ (1 << (cbits -2)) -1 :x})')
		##
	print(f'#define  SAT_TEMPL_1_OF_N{ len(vars) }_IS_NEGATIVE  ' +
			f'UINT{ cbits }_C(0x{ 1 << (cbits -1) :x})')
		##
	print(f'#define  SAT_TEMPL_1_OF_N{ len(vars) }_IS_ADDED_VAR ' +
			f'UINT{ cbits }_C(0x{ 1 << (cbits -2) :x})')
	print("/**/")

	print(f'#define  SAT_TEMPL_1_OF_N{ nrvars }_INPUT_VARS   ' +
			f'((unsigned int) { nrvars })')
	print(f'#define  SAT_TEMPL_1_OF_N{ nrvars }_ADDL_VARS    ' +
			f'((unsigned int) { addvars })')
	print(f'#define  SAT_TEMPL_1_OF_N{ nrvars }_CLAUSES      ' +
			f'((unsigned int) { nrcls })')
	print(f'#define  SAT_TEMPL_1_OF_N{ nrvars }_MAX_CLS_VARS ' +
			f'((unsigned int) { maxv  })')
	print(f'#define  SAT_TEMPL_1_OF_N{ nrvars }_VARBITS      ' +
			f'((unsigned int) { cbits })')
	print(f'#define  SAT_TEMPL_1_OF_N{ nrvars }_ELEMS        ' +
			f'((unsigned int) { ccnt })')
	print("/**/")
	print(f'static const {ctype} SAT_TEMPL_1_OF_N{ nrvars }' +
		f'[{ ccnt }] = {{')

	for ci, c in enumerate(ct):
		print(",".join(f"{cf}"  for cf in c)  +",")

		if ci == 0:
			print('// /header')
			print('//')

	print('} ;')
	print('// /CLAUSES')

				## entries to include to template's struct
				## see sat.c
				##
	tentry = [
		f'#define  SAT_TEMPL_1_OF_N{ nrvars }_FULL \\',
		f'{{ { nrvars }, \\',
		f'  SAT_TEMPL_1_OF_N{ nrvars }_VARBITS,      \\',
		f'  SAT_TEMPL_1_OF_N{ nrvars }_MASK,         \\',
		f'  SAT_TEMPL_1_OF_N{ nrvars }_IS_NEGATIVE,  \\',
		f'  SAT_TEMPL_1_OF_N{ nrvars }_IS_ADDED_VAR, \\',
		f'  SAT_TEMPL_1_OF_N{ nrvars }_INPUT_VARS,   \\',
		f'  SAT_TEMPL_1_OF_N{ nrvars }_ADDL_VARS,    \\',
		f'  SAT_TEMPL_1_OF_N{ nrvars }_CLAUSES,      \\',
		f'  SAT_TEMPL_1_OF_N{ nrvars }_MAX_CLS_VARS, \\',
		f'  (const void *)                           \\',
		f'      SAT_TEMPL_1_OF_N{ nrvars },          \\',
		f'  SAT_TEMPL_1_OF_N{ nrvars }_ELEMS,        \\',
		'}',
	]
	##
	print('\n'.join(tentry))

	print('// /GENERATED.SRC')
	print('// }')
	print()


##============================================================================
def template2python(t):
	sys.exit(0)


##======================================
if __name__ == '__main__':
	sat  = satsolv_init0()
	vars = []

	BITS = 4
	if 'BITS' in os.environ:
		BITS = int(os.environ['BITS'])

	maxn    = 128
	vdigits = log10(BITS)

	vars = [f'v{v:0{vdigits}}'  for v in range(maxn)]

	if 'TEMPLATE' in os.environ:
		if 'OR' in os.environ[ 'TEMPLATE' ]:
			print(f'[  ## OR(1..{maxn}) templates, 0-based index')
			for vb in range(1, maxn+1):
				t = satsolv_or('', vb, negate=False,
				               force=False, template=True)
				print('\t', t)
			print(']\n')

		if 'AND' in os.environ[ 'TEMPLATE' ]:
			print(f'[  ## AND(1..{maxn}) templates, 0-based index')
			for vb in range(1, maxn+1):
				t = satsolv_and('', vb, negate=False,
				                force=False, template=True)
				print('\t', t)
			print(']\n')

		if '1OFN' in os.environ[ 'TEMPLATE' ]:
			print(f'[  ## 1-of-N(1..{maxn}) templates, 0-based index')
			for vb in range(1, 32+1):    ## range(1, maxn+1):
				t = satsolv_1ofn_2prod(None, vb, allow0=False,
				                force=True, template=True)
				print('\t', t)
			print(']\n')

		sys.exit(0)
		##-------------------------------

		if os.environ[ 'TEMPLATE' ] == '1OFN':
			r, nvars, cls, comm = satsolv_1ofn_2prod(sat,
			                                   vars[ :BITS ])
		print(f'## 1-of-N[{ BITS }] r={r} cls[{len(cls)}]',
		      nvars, comm)

		clauses2print(cls, vars[ :BITS ], nvars, r)

		sys.exit(0)

	##----- 1-of-N, 1..65  ------------------

	for vb in range(1, 65):
		sat  = satsolv_init0()

		satsolv_add_vars(sat, vars[:vb])

		r, nvars, cls, comm = satsolv_1ofn_2prod(sat, vars[:vb])
		print(f'## 1-of-N[{ vb }] r={r} cls[{len(cls)}]={ cls }',
		      nvars, comm)

		sat_report_vars(sat, prefix='//')

		clauses2print(cls, vars[:vb], nvars, r)

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
		many_noneq0(BITS)

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

	cls, neq, comm = satsolv_neq_or0(sat, vars[:BITS], vars[BITS:],
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

