#!/bin/sh

## generate less-than-N templates, N=1..4095

export D=/tmp/sat

for l in $( seq 1 4095 ) ; do
	TEMPLATE_LT=$l ./sat | tee $D/lt$( printf "%04d" $l ).cnf
done

#--------------------------------------------------------
exit

## check all less-than-N input combinations for 1..4095

export TT=~/prj/src.tmp/pack/dev/truthtable-cnf.py
export TA=~/prj/src.tmp/pack/dev/truthtable2assign.py
export D=/tmp/sat

export TRACE=1
(
for l in $( seq 1 4095 ) ; do
	echo limit=$l
	export LIMIT=$l
	$TT | $TA $D/lt$( printf "%04d" $LIMIT ).cnf
	echo
done ) |& tee -a $D/lt-all.log

#--------------------------------------------------------
exit

## generate not-equal-or-0 templates, N=1..12

export D=/tmp/sat

for l in $( seq 1 12 ) ; do
	TEMPLATE_NEQ0=$l ./sat | tee $D/neq0-$( printf "%04d" $l ).cnf
done

#--------------------------------------------------------

## check all not-equal-or-0 input combinations for (2x) 1..12 bits

export TT=~/prj/src.tmp/pack/dev/truthtable-cnf.py
export TA=~/prj/src.tmp/pack/dev/truthtable2assign.py
export D=/tmp/sat

export TRACE=1
(
for l in $( seq 1 12 ) ; do
	BITS=$l $TT | $TA $D/neq0-$( printf "%04d" $l ).cnf
	echo
done ) |& tee -a $D/neq0-all.log

#--------------------------------------------------------
#--------------------------------------------------------
exit

