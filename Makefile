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


$(BASEXY_C): $(BASEXY)
	$(shell tr '\t' , < $^ > $@)


##--------------------------------------
CLEAN := packnroute.txt

clean: $(wildcard $(CLEAN))
	$(RM) $(wildcard $(CLEAN))

.PHONY: clean
.PRECIOUS: packnroute.txt
