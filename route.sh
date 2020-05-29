#!/bin/sh

## MUST be able to read input repeatedly

PATHFILE=path256x256.txt
PATHFILE=path64x64x4.txt
PATHFILE=path64x64.txt

RANGEMAX=64
PIXELS=1024
DIR=r

##--------------------------------------
[ ! -d $DIR ] && mkdir $DIR

##--------------------------------------
N=$( pars --count $@ )
echo $N total frames incl. starting one

##--------------------------------------
## +10% margin on plot
##
echo "#PLOT set xrange [0:$(( ( $RANGEMAX *110 + 99 ) / 100 ))]"
echo "#PLOT set yrange [0:$(( ( $RANGEMAX *110 + 99 ) / 100 ))]"

echo "#PLOT # bright red points+lines"
echo "#PLOT set style line 1 lc rgb '#d00000' lw 2 ps 1 pt 7"

echo "#PLOT # faint grey for grid"
echo "#PLOT set style line 2 lc rgb '#808080' lw 1 ps 1 pt 0"


##--------------------------------------
echo "#PLOT set terminal png size $PIXELS,$PIXELS"
echo "#PLOT set output 'r/000000.png'"

pars --cut 1 $@ | grep -v = | sed 'sQ^# *QQ;sQ,Q Qg' > r/000000

echo "#PLOT set title ' '"
echo -n "#PLOT plot \"${PATHFILE}\" with lp ls 2, \""
echo    r/000000"\" with p ls 1"
echo    "#PLOT"
echo


##--------------------------------------
for i in $( enum 2 $N ) ; do
	ID=$( printf "%06u" $(( 10#$i - 1 )) )
	echo id=$ID

	pars --cut $i $@ | grep -v = | sed 'sQ,Q Qg' > r/$ID ## | \
		##grep -v '^#' > r/$ID

	dist=$( pars --cut $i $@ | grep DIST )
	dist=${dist##*DIST=}
##	dist=$( printf "%.1f" $dist )

	echo "#PLOT set terminal png size $PIXELS,$PIXELS"
	echo "#PLOT set output 'r/${ID}.png'"

		## TODO: show pct change
		##
	echo "#PLOT set title 'DIST%[$ID]'"

	echo -n "#PLOT plot \"${PATHFILE}\" with lp ls 2, \""
	echo    r/${ID}"\" with lp ls 1"

	echo    "#PLOT"
	echo
done

