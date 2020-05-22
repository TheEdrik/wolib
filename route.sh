#!/bin/sh

## MUST be able to read input repeatedly

PATHFILE=path256x256.txt
PATHFILE=path64x64x4.txt

##--------------------------------------
N=$( pars --count $@ )
echo $N total frames incl. starting one

##--------------------------------------
## assume 256x256 grid
##
echo "#PLOT set xrange [0:280]"
echo "#PLOT set yrange [0:280]"

echo "#PLOT # bright red points+lines"
echo "#PLOT set style line 1 lc rgb '#d00000' lw 2 ps 1 pt 7"

echo "#PLOT # faint grey for grid"
echo "#PLOT set style line 2 lc rgb '#808080' lw 1 ps 1 pt 0"


##--------------------------------------
echo "#PLOT set terminal png size 800,800"
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

	echo "#PLOT set terminal png size 800,800"
	echo "#PLOT set output 'r/${ID}.png'"

		## TODO: show pct change
		##
	echo "#PLOT set title 'DIST%[$ID]'"

	echo -n "#PLOT plot \"${PATHFILE}\" with lp ls 2, \""
	echo    r/${ID}"\" with lp ls 1"

	echo    "#PLOT"
	echo
done

