#!/bin/sh
# full G* census on the PW grid cells with n <= 6 and (n+1)^m <= 3e8 (k4/haxell.md §5); runs after run_pw.sh
cd "$(dirname "$0")"
L=../../results/k4_haxell
while [ ! -f $L/pw_done.flag ]; do sleep 20; done
cc -O2 -o gstar gstar.c
python3 gstar_run.py pwgrid NMAX=6 MMAX=13 MAXSTATES=300000000 SHOW=40 > $L/gstarc_pwgrid.log 2>&1
echo ALLDONE > $L/pwcensus_done.flag
