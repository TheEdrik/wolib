#!/usr/bin/python3

## turn back standalone SAT-solver output to packer-readable form
##
## requires pack-and-route result (for variable/name mappings) and
## SAT solver DIMACS output
##
## see satsolv_report() in pack-and-route for formatting. we extract
## the VARIABLES section:
##     -----------------------
##     c VARIABLES:
##     c   d0t2[1] d0t2v0[2] d0t2v1[3] d0t2v2[4] d0t2v3[5] d0t2v4[6]
##     c   d0t3[7] d0t3v0[8] d0t3v1[9] d0t3v2[10] d0t3v3[11] d0t3v4[12]
##     ...
##     c /VARIABLES
##     -----------------------
##         (1) tolerate+ignore leading "c ...whitespace..." (DIMACS comment)
##         (2) IDs are all-letter+digit
##         (3) numeric indexes are >0
##
## response (only minimal parsing):
##     -----------------------
##     ...
##     s SATISFIABLE
##     v -1 -2 -3 -4 -5 -6 7 8 -9 ...
##     ...
##     v -13098 -13099 0
##     ...
##     -----------------------
##         response processing stops at the first "0"
##
## DIMACS format (simplified version):
##     Jaervisalo, Le Berre, Roussel: Rules of the 2011 SAT competition
##     www.satcompetition.org/2011/rules.pdf, section 4.1
## accessed 2023-02-27
## SHA1()=xb08ad0aca66821ee85fb8e05650340f6180db386
## SHA256()=xcab5a36e6dda3efef32be201838012d03a901c04ef3556762442b5010aaeb479
##
## we expect to read entire files, and not use a streaming API.
## please do not comment on inefficiency, or the expectation that
## we only deal with reasonably small inputs.
##
## Author: Visegrady, Tamas  <tamas.visegrady@gmail.com>

import re, sys, fileinput


##-----------------------------------------
reVARDEF = re.compile('(?P<id> [a-zA-Z0-9]+) \[ (?P<nr> \d+) \]',
                      re.VERBOSE)
##
## match "d0t4v0[14]" -> id = d0t4v0, nr = 14


reOK = re.compile('^ s \s+ SATISFIABLE$ ', re.VERBOSE)

reRESPONSES = re.compile('^ v \s+', re.VERBOSE)


##-----------------------------------------
## retrieve VARIABLES section, populate reverse maps
## return None if file is not recognized
##
## registers keys (ints) >0
## tolerate repeated identical assignments; ensures mapped-int unicity
##
def vars2list(lines):
	matches = list(li  for li, l in enumerate(lines)
	                   if re.search('VARIABLES', l))

	if len(matches) != 2:
		return None

	all = list(re.sub('^c\s+', '', l)  for l in lines)

	if ('/VARIABLES' in all[ matches[0] ]):
		sys.stderr.write("no VARIABLES start tag; " +
				"is this really our SAT-solver input?\n")
		return None

	if not ('/VARIABLES' in all[ matches[1] ]):
		sys.stderr.write("no /VARIABLES terminating tag; " +
					"accepting possibly partial input\n")

	all = all[ matches[0]+1 : matches[1] ]
	res = {}

	for l in (r.split()  for r in all):
		for elem in l:
			m = re.match(reVARDEF, elem)
			if m == None:
				sys.stderr.write("can not parse SAT-variable " +
					f"assignment ({elem})\n")
				return None

			id, nr = m.group('id'), m.group('nr')

			if nr == 0:
				sys.stderr.write("invalid SAT-variable ID 0\n")
				return None

					## tolerate identical redefinitions
					## report other
			if nr in res:
				if res[ nr ] == id:
					continue
				sys.stderr.write("invalid SAT-variable " +
					f"redefinition ({nr}: {id} vs. " +
					f"{ res[nr] })\n")
				return None
			else:
				res[ nr ] = id

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
## map back integers from 'vars' to string inputs
## 'lut' is integer-to-table, containing >0
##
## response maps True/False to all inputs, or None if not defined
##
def satsolv_ints2strings(vars, lut):
	res = dict.fromkeys(lut.values())        ## default value None

	for r in vars:
					## split each to sign ('-' or empty)
					## and base string
		signs, curr = satsolv_str2ids(r.split())

		for i, nr in enumerate(curr):
			if nr == '0':
				break

			if not nr in lut:
				sys.stderr.write(f"ERROR: unknown variable "+
						f"ID: [{ id }]\n")
				return None

			id = lut[ nr ]
			v  = (signs[i] != '-')

					## tolerate identical redefinition
			if (res[ id ] != None) and (res[ id ] == v):
				continue

			res[ id ] = v

	return res


##-----------------------------------------------------------
if __name__ == '__main__':
	if len(sys.argv) < 2:
		sys.stderr.write(
			"Recover pack+route variables from SAT solver log.\n"
			"Usage: <...solver input...> " +
			"[...SAT-solver response...]\n")
		sys.exit(2)

	try:
		vars = open(sys.argv[1], 'r').read().split("\n")
		sys.argv.pop(1)
	except:
                sys.stderr.write(f"ERROR: read [{ sys.argv[1] }] failed\n")
                sys.exit(1)

	v2ints = vars2list(vars)
	if v2ints == None:
                sys.stderr.write(f"ERROR: invalid ID-to-number mapping\n")
                sys.exit(1)

	lines = list(fileinput.input())
	ok    = list(li  for li, l  in enumerate(lines)  if re.match(reOK, l))
	if (len(ok) != 1):
                sys.stderr.write(f"ERROR: does not look like a solved "
				"SAT problem response\n")
                sys.exit(1)

	lines = list(re.sub(reRESPONSES, '', l)  for l in lines[ ok[0]+1 : ]
	             if re.search(reRESPONSES, l))

	res = satsolv_ints2strings(lines, v2ints)

	for r in sorted(res.keys()):
		print(f'  { r }: { res[r] }')

