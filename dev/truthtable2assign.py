#!/usr/bin/python3

##--------------------------------------
## read CNF from SAT solver. MUST have been constructed such that
## variables 1..N are free variables, or top-level outputs. (In other
## words, assign free inputs first, then top-level outputs, and
## leave intermediate variables at the end of the CNF list.)
##
## Usage: ... <CNF file> [truth table/file...]
##
## set 'NEVER' in environment if the formula MAY switch to unsolvable
## based on its inputs alone. In those cases, we special-case unsolvable
## results if they are consistent with the expected result, so
## 'unsolvable' is interpreted as OK if the expected result is False.
##
## Author: T Visegrady <tamas.visegrady@gmail.com>

## CNF template/input:
##    > p cnf 28 63
##    > c CONSTRAINTS:
##    > c NEQ-OR0[4b](v0_0,v0_1,v0_2,v0_3 / v1_0,v1_1,v1_2,v1_3)  ## 2x 4 bits
##    > ...
##    > 1 2 3 4 10 0
##    > -1 10 0
##    > -2 10 0
##    > ..
##    > 16 10 11 -9 0
##    > -16 9 0
##    > -10 9 0
##    > -11 9 0
##             ## note: free inputs 1..8; single-bit result is variable nr. 9
##
## read variable assignments, one per line (N 0/1 assignments). Assign
## to variables 1..N; verify against SAT solver.
##    > 0 1 0 1  0 1 0 0  1                     ## 2x 4 bits (inputs) +1 result
##        -> -1, 2, -3, 4, -5, 6, -7, -8, 9     ## CNF form
##
## SAT solver config hardwired in solve()


import fileinput, sys, subprocess, os


##--------------------------------------
## directly CNF-usable assignment corresponding to int list 'vars'
## adds one clause for each 'vars' element
##
def vars2cnf(vars):
	return '\n'.join(f'{v} 0'  for v in vars)


##--------------------------------------
## pass template plus assignments through external SAT solver
##
## returns True if solver accepted, False otherwise
## raises exception if can not parse solver, or it reports an unexpected error
##
def solve(header, template, vars):
	curr = vars2cnf(vars)

	args = [ 'kissat', ]

	if True or 'RELAX' in os.environ:
		args.append( '--relaxed' )     ## tolerate inconsistent clause
		                               ## or variable count

	svr  = subprocess.Popen(args, stdin=subprocess.PIPE,
	                        stdout=subprocess.PIPE)

				## add 'vars' clauses to what was in header
				## only clauses, but not variables
	p = header.split()
	if len(p) == 4:         ## "p cnf <..nr.variables..> <..nr.clauses..>"
		nrclauses = int(p[3], 10)
				## TODO: handle exceptions, not just exit
		nrclauses += len(vars)
		p.pop(3)
		p.insert(4, str(nrclauses))
		header = ' '.join(p)

	svr.stdin.write(header.encode('utf8') +b'\n')
	svr.stdin.write(template.encode('utf8') +b'\n')
	svr.stdin.write(curr.encode('utf8') +b'\n')

	res = svr.communicate()                       ## returns (stdout, None)
	r   = res[0].split(b'\n')

			## DIMACS ensures single ASCII space as separator
	ok   = (b's SATISFIABLE'   in r)
	fail = (b's UNSATISFIABLE' in r)

	if ok == fail:
		raise ValueError("can not parse SAT solver response")

	return ok


##--------------------------------------
if __name__ == '__main__':
	seen = 0

	if (len(sys.argv) < 2):
		sys.stderr.write("need CNF file input\n")
		sys.exit(1)
	try:
		cnf = open(sys.argv[1], 'r')
	except:
		sys.stderr.write(f"ERROR: can not open CNF ({sys.argv[1]})\n")
		sys.exit(-1)
	cnf = cnf.read()
	sys.argv.pop(1)

## TODO: adjust line with clause count
				## extract header; cnf is all remaining lines
				## we update header to add our clauses' counts

	cnflines = cnf.split('\n')
	if (cnflines == []) or (cnflines[0][:2] != 'p '):
		sys.stderr.write(f"ERROR: CNF does not start with header")
		sys.exit(-1)

	header = cnflines.pop(0)
	cnf = '\n'.join(cnflines)

	minvars, maxvars = 9999999999, -1
			## maxvars set to None if we ever see different nr.
			## of input variables
			##
			## our truth table generator only outputs uniform
			## lines -> can extrapolate nr. of remaining ones

	for l in (l.rstrip('\n') for l in fileinput.input(openhook=
	                                  fileinput.hook_encoded("utf-8"))):

					## bits(original); vars(+-integer)
		try:
			bits = list(int(b) for b in l.split())
			vars = list((f'{bi+1}' if (b == 1) else  f'-{bi+1}')
			            for bi, b in enumerate(bits))
		except:
			continue
		if not vars:
			continue

		if maxvars != None:
			minvars = min(minvars, len(vars))
			maxvars = max(maxvars, len(vars))
			##
			if minvars != maxvars:
				maxvars = None

		seen += 1

		s = solve(header, cnf, vars)

			## no solution
			##
			## an 'it depends' situation: either we encountered
			## a real failure, or the combination is simply
			## invalid
			## -> check expected output. 'NEVER' allows cross-
			## check against expected result. (False there,
			## with an UNSATISFIABLE report, is interpreted
			## as OK)
			##
		if (s == False):
			if ('NEVER' in os.environ):
				if bits[-1] == 0:      ## expected result=False
					s = True
			else:
				if bits[-1]:
					sys.stdout.write("unexpected failure")
					sys.stderr.flush()
		else:
			if bits[-1] == 0:
				sys.stdout.write("unexpected success")
				sys.stderr.flush()
## TODO: centralized terminate() macro

##
## TODO: hardwired nr. of result bits (1)

		if s == False:
			print(f"nr. of combinations: {seen}")
			print('ERROR: invalid combination:')
			print(f'  input={ vars }[orig: { bits }]')

			print('===SAT:=============================')
			print(header)
			print(cnf)
			print(vars2cnf(vars))
			print('===/SAT=============================')
			sys.stdout.flush()
			sys.stderr.flush()
			sys.exit(1)

		if seen and ((seen % 100) == 0):
			if (seen > 5000) and (maxvars != None):
				pass           ## expected nr. of combinations

			print(f"seen {seen}")
			if False:
				print('...of N...')
			sys.stdout.flush()

	sys.stderr.write('all verified\n')
	sys.exit(0)

