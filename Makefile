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
sat: packnroute.txt
	grep SAT= $^ | sed 'sQSAT=QQ'           > p.sat
	time cryptominisat5 --verb 2 p.sat      | tee p.solv
	dev/sat2back.py p.sat p.solv            | tee pnr.log 
	grep -v -e ' NV' -e _x_ -e _nn_ pnr.log | tee pnr2.log


$(BASEXY_C): $(BASEXY)
	$(shell tr '\t' , < $^ > $@)


##--------------------------------------
CLEAN := packnroute.txt p.sat p.solv pnr.log pnr2.log

clean: $(wildcard $(CLEAN))
	$(RM) $(wildcard $(CLEAN))


.PHONY: clean sat
.PRECIOUS: packnroute.txt
