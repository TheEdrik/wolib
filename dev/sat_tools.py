## utility functions shared by dev and runtime code

import re

##----------------------------------------------------------------------------
## iterator returning only clauses
##
def dimacs2clauses_itr(dimacs):
	in_lead = True

	for di, d in enumerate(dimacs):
		if d.startswith('p') or d.startswith('c'):
			if in_lead:
				continue
			raise ValueError("malformed DIMACS lead/comment " +
					f"(line {di}) ({d})")

		in_lead = False
		yield d


##--------------------------------------
## list of all comments, in original order
##
## TODO: return list of leading whitespace (which has been stripped)
##
## preserves all-empty comment lines as '', except for those immediately
## after header line
##
## TODO: yes, we are aware that regex-counting lead size is slow
##     stackoverflow.com/questions/13648813/
##         what-is-the-pythonic-way-to-count-the-leading-spaces-in-a-string
##
def dimacs2comments(dimacs):
	stage = 1      ## header(1), empty lead(2), comments(3), all beyond (4)
	               ## (2) and (3) are both optional

	for di, d in enumerate(dimacs):
		if d.startswith('p'):
			if stage == 1:
				stage = 2
				continue
			raise ValueError("malformed DIMACS lead " +
					f"(line {di}) ({d})")
			
		if d.startswith('c'):
			if (stage < 2) or (stage >= 4):
				raise ValueError("misplaced DIMACS comment " +
						f"(line {di}) ({d})")
			craw = re.sub('^c\s*', '', d)

			if craw:
				stage = 3  ## past optional-lead empty comments
			if craw or (stage == 3):
				yield craw
			continue

		stage = 4
		return


##----------------------------------------------------------------------------
def comments2print(comm):
	for c in comm:
		yield f'c {c}'


##----------------------------------------------------------------------------
## TODO: add mappings
def clauses2print(cls):
	for c in cls:
		craw = ' '.join(f'{v}' for v in c)
		yield craw + ' 0'


##----------------------------------------------------------------------------
## read DIMACS spec (input); parse complete list of clauses
## returns net clause list, excluding any terminating 0's
##
## TODO:
## input may be raw input file, or list of its lines [net, already \n-stripped]
##
## without 'strict', accepts any non-whitespace ID as valid
## such as when processing
##
def dimacs2clauses(dimacs, strict=True):
	res = [ [] ]

	for c in (d.split() for d in dimacs):
		try:
			clist = [ int(v)  for v in c ]
		except:
			if strict:
				raise ValueError("non-numeric CNF variable" +
					f"({d})")
			clist = c

		for ci in clist:
			if (ci != 0) and (ci != ''):
				res[-1].append(ci)
			else:
				if res[-1] != []:
					res.append([])
	if (res[-1] == []):
		res.pop(-1)

	return res


##--------------------------------------
## parse limits of clauses' list-of-int-lists format
## returns max. variable index referenced; set of variables actually used
##
def clauses2varlimits(clauses):
	maxv, seen = -1, set()

	for c in clauses:
		cabs =  [ abs(v)  for v in c ]
		maxv =  max(maxv, max(cabs))
		seen |= set(cabs)

	return maxv, seen


##--------------------------------------
## inner core of template_specialize()
## 'x' is variable (numeric) which is known
##
## TODO: restricted to removing 'True' fixed values
##
## returns None if there are no affected clauses
## specialized/shortened clause list otherwise
##
def clauses_specialize(cls, x):
	res = []

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
			pass        ## 'X' is present; entire clause is skipped

		else:
			res.append(ints2renumber(c, x))

	return res


