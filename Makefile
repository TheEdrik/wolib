## see gen-packnroute.py for some of the auxiliary files


			## 5-column list of orders
			## primary weight,  X,  Y,  time window/s,  delv.ID
ORDERS := orders1.txt

			## tab-separated list of bases, each line X <tab> Y
BASEXY := bases1.txt
			## compressed form X,Y[:X2,Y2...]
			## DO NOT DIRECTLY EDIT
BASEXY_C := bases1c.txt
			## tr '\t' , < base1s.txt > bases1c.txt
## TODO: direct shell include

			## XY pairs' list, associated distances (JSON)
DISTANCES := distance.json

			## tracing, see list in pack.py
TRACE := sched,pack,stack,flow,map

			## level, if set
DEBUG := 1

SAT := 1                ## produce SAT solver expression
                        ## note: requires XY-to-distance(time) table

SAT_V := +4             ## nr. of vehicles to consider, relative to
                        ## rough-estimate minimum (+...)

SAT_DEBUG := 1

##--------------------------------------
all: packnroute.txt


packnroute.txt:  $(ORDERS)  $(BASEXY_C)  $(DISTANCES)
	BASE=$(shell cat $(BASEXY_C)) DIST=$(DISTANCES)                 \
		TRACE=$(TRACE) DEBUG=$(DEBUG)                           \
		SAT=$(SAT) SAT_VEHICLES=$(SAT_V) SATDEBUG=$(SAT_DEBUG)  \
		MAX1=8542700000 TUPLE_N=6 NONSEL=1                      \
		./pack.py  $(ORDERS) n=$(R) | tee $@


##--------------------------------------
## (1) extract SAT-solver input from pack-and-route log
## (2) pass through solver
## (3) match solver variables to original symbolic forms (which are stored
##     as comments in solver input)
## (4) extract directly schedule-relevant variables
##
## with intermediate/partial input, there may be missing variables
## or clauses.  kissat, as an example, requires the '--relaxed' flag
## to process such incomplete input.  (cryptominisat does not.)
##
sat: packnroute.txt
	grep ^SAT= $^ | sed 'sQSAT=QQ'          > p.sat
	kissat -s -v -v p.sat                   | tee p.solv
	dev/sat2back.py p.sat p.solv            | tee pnr.log
	grep -v -e ' NV' -e _x_ -e _nn_ pnr.log | tee pnr2.log

## cryptominisat invocation above:
## time cryptominisat5 --verb 2 p.sat      | tee p.solv

$(BASEXY_C): $(BASEXY)
	$(shell tr '\t' , < $^ > $@)


##--------------------------------------
## retrieve XY list -> turn into distances' table
##
## not automatically remade; think of adjusted/corrected tables
##
$(DISTANCES): $(ORDERS)
	MAX1=99999999999 XY2TABLE=1 ./pack.py $(ORDERS) > $@


##--------------------------------------
## sample SAT/truth table cross-check:
##   (1) generate SAT expression as template. only expression, standalone;
##       assign inputs as 1..N-1, and output bits as N [N+1...].  in other
##       words, leave intermediate bits after any of these
##
##     (1.1) output is ...template... below
##
##   (2) enumerate truth tables; expect this to be ~arbitrarily large
##
##     (2.1) see dev/truthtable-cnf.py for function-to-truth.table conversions
##
##   (3) use dev/truthtable2assign.py to check all truth table combinations
##       against template.  internally, each combination is added as a set
##       of clauses and passed through a solver.  any failing combination
##       stops the stream.
##
## assume ...template... is already available, and truthtable-cnf.py is
## configured to output the full truth table without any parameters:
##
##   dev/truthtable-cnf.py | dev/truthtable2assign.py | tee cnffail.txt && \
##       sed '1,/SAT:/d;/\/SAT=/{d;q}' cnffail.txt | tee cnffail.sat
##
## the first failing combination will be saved cnffail.sat, including
## its context in cnffail.txt:
##
##    ERROR: invalid combination:
##      input=[-1, -2, 3, -4, -5, 6, -7][orig: [0, 0, 1, 0, 0, 1, 0]]
##    ===SAT:=============================
##    p cnf 13 28
##    c
##    c CONSTRAINTS:
##    c   NEQ-OR0[3b](v0_00,v0_01,v0_02 / v1_00,v1_01,v1_02)
##    c /CONSTRAINTS:
##    ...
##    c VARIABLES:
##    c   v0_00[1] v0_01[2] v0_02[3] v1_00[4] v1_01[5] v1_02[6] NEQ[7]
##    c   NOR1[8] NOR2[9] XOR3[10] XOR4[11] XOR5[12] NEQ6[13]
##    c /VARIABLES 
##    c
##    1 2 3 8 0
##    -1 8 0 
##    -2 8 0 
##    ...


##--------------------------------------
CLEAN := packnroute.txt p.sat p.solv pnr.log pnr2.log

clean: $(wildcard $(CLEAN))
	$(RM) $(wildcard $(CLEAN))


.PHONY: clean sat
.PRECIOUS: packnroute.txt

