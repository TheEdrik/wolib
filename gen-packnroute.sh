#!/usr/bin/sh

# generate random delivery list and its auxiliary files
#
# NOSHARE=...time.spec... generates N deliveries which are all in the
# same time unit (-> can not share vehicles)

## number of items, final output
##
ITEMS=${ITEMS:-200}
DELIVERIES=${DELIVERIES:-orders.txt}

## boundary file
## generated points all fall within boundary
##
## X,Y coordinate pairs, one per line, in border-traversal order
##
## note: keep test examples 0.0--1.0 normalized (both X and Y coordinates),
##       or at least bounded
##
BORDER=${BORDER:-budapest0.txt}

## XY(pairs)-to-distance/cost lookup table
## {
## "points":[[X0, Y0], [X1, Y1], ... ],
## "time": [[0.0, XY0-to-XY1 cost, ... ],
##          [XY1-to-XY0 cost, 0.0, ... ],
## ],
## }
## coordinates stored as strings: we want exact matching for lookups,
## not subject to FP rounding etc.
##
DIST=distance


## example files
##     base0.txt:
##         0.625  0.625     ## tab-separated
##
## turn into comma-separated list
##     tr '\t' , < bases1.txt


##-----  nothing user-serviceable below  -------------------------------------

##--------------------------------------
## special corner conditions
##
## deliveries in the same time window: N of them require exactly N
## vehicles

if [ -n "$NOSHARE" ] ; then
	TF=/tmp/order0.txt
	RNITEMS=$ITEMS RNTIME=1 RNCOORDS=${BORDER} ./pack.py > $TF

#	if [ ] ; then
#	else
		HR=$(( 9 + ( $RANDOM % 6 ) ))
		MIN=$(( ($RANDOM % 4) * 15 ))

		HRE=$( printf "%02d" $(( $HR + ( ( $MIN + 15 ) / 60 ) )) )
		MNS=$( printf "%02d"      $MIN               )
		MNE=$( printf "%02d" $(( ($MIN + 15) % 60 )) )

		SAMETIME=$( printf "%02d" $HR )${MNS}-${HRE}${MNE}
#	endif

	sed -E "sQ,[^,]+,unitQ,${SAMETIME},unitQ" $TF | tee $DELIVERIES
	exit
fi


##--------------------------------------

## generate order list in extended-format input, incl. random
## XY coordinates and delivery times
##
RNITEMS=$ITEMS RNTIME=1 RNCOORDS=${BORDER} ./pack.py > $DELIVERIES

## table for XY(pair)-to-distance lookup
MAX1=99999999999 XY2TABLE=1 ./pack.py $DELIVERIES > $DIST.json

## C table, include-ready structures for standalone solver
MAX1=99999999999 XY2TABLE=1 TO_C=1 ./pack.py $DELIVERIES > $DIST.c

## pack-and-route, using base from 'bases1.txt', and above generated
## XY-to-distance lookup table
##
MAX1=8542700000 BASE=$( tr '\t' , < bases1.txt ) DIST=distance.json \
	./pack.py orders.txt > $DIST.log

