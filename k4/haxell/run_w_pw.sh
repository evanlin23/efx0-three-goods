#!/bin/sh
# Conjecture W on the PW grid cells small enough for the measure checker (k4/haxell.md §6); after run_pw_census.sh
cd "$(dirname "$0")"
L=../../results/k4_haxell
while [ ! -f $L/pwcensus_done.flag ] || [ ! -f $L/highk_done.flag ]; do sleep 30; done
python3 gstar_measure_run.py pwgrid NMAX=5 MMAX=11 MAXSTATES=12000000 RADIUS=2 ROT=1 > $L/measure_rot2_pwgrid.log 2>&1
echo ALLDONE > $L/wpw_done.flag
