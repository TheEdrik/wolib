#!/usr/bin/python3

## construct SAT-solver expressions for solving vehicle routing subproblems

import re


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

	cls.extend([                         ## truth table for "{lf} XOR {rg}"
		f' {lf}  {rg} -{cmd}',
		f'-{lf}  {rg}  {cmd}',
		f' {lf} -{rg}  {cmd}',
		f'-{lf} -{rg} -{cmd}',
	])

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
	nof1(256)

