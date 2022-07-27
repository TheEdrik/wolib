#!/usr/bin/sh

# generate random delivery list and its auxiliary files

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
DIST=distance.json


##-----  nothing user-serviceable below  -------------------------------------

## generate order list in extended-format input, incl. random
## XY coordinates and delivery times
##
RNITEMS=$ITEMS RNTIME=1 RNCOORDS=${BORDER} ./pack.py > $DELIVERIES

## table for XY(pair)-to-distance lookup
MAX1=99999999999999999 XY2TABLE=1 ./pack.py $DELIVERIES > $DIST

