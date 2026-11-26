#!/bin/sh
# CONN_2 on other workstreams' counterexamples (k4/haxell.md §5); logs in results/k4_haxell/
cd "$(dirname "$0")"
L=../../results/k4_haxell
cc -O2 -o gstar gstar.c
python3 gstar_run.py ext NMAX=6 MMAX=10 MAXSTATES=300000000 SHOW=20 > $L/gstarc_ext.log 2>&1
python3 gstar_run.py ttc NMAX=6 MMAX=10 MAXSTATES=300000000 SHOW=40 > $L/gstarc_ttc.log 2>&1
python3 gstar_run.py bcore NMAX=6 MMAX=10 MAXSTATES=300000000 SHOW=4 > $L/gstarc_bcore.log 2>&1
echo ALLDONE > $L/ext_done.flag
