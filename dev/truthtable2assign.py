#!/usr/bin/python3

##--------------------------------------
## read truth table; turn into one file each, which lists variables
## in SAT-CNF form.  suitable to concatenate with generated SAT-CNF
## form; ensures listed combinations plus all our extracted
## forms together are satisfiable.
##
## variables assumed to have index 1..N


import fileinput, sys


##--------------------------------------
if __name__ == '__main__':
	count, idx = False, 0

	if (len(sys.argv) > 1) and (sys.argv[1][0] == '-'):
		if (sys.argv[1] == '--count'):
			count = True
		else:
			idx = int(sys.argv[1][1:])
		sys.argv.pop(1)

	all = (l.rstrip('\n') for l in fileinput.input(openhook=
	                               fileinput.hook_encoded("utf-8")))
	all = list(l  for l in all  if (('1' in l) or ('0' in l)))

	if count:
		print(len(all))
		sys.exit(0)

	if idx >= len(all):
		sys.exit(1)

	bits = list(int(b) for b in all[ idx ].split())

					## CNF clauses, one bit per line
					## -(...false index...) 0   OR
					##  (...true index...)  0
	for bi, b in enumerate(bits):
		print(f'{bi+1} 0' if  (b == 1) else  f'-{bi+1} 0')

