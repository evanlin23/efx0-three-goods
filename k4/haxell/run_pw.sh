#!/bin/sh
# CONN_2 at k >= 5 (k4/haxell.md §5): the clean PW(f, W, r) grid (f <= 5, W <= 4, r <= 8, so k = max(r+1, f+1) <= 9),
# full census where (n+1)^m <= 3e8, start-based probes on every cell; logs in results/k4_haxell/
cd "$(dirname "$0")"
L=../../results/k4_haxell
cc -O2 -o gstar gstar.c
cc -O2 -o gstar_probe gstar_probe.c 2>/dev/null
python3 gstar_run.py pwgrid NMAX=6 MMAX=13 MAXSTATES=300000000 SHOW=20 > $L/gstarc_pwgrid.log 2>&1
python3 gstar_probe_run.py pwgrid CAP=2000 WALK=3 LEN=6 ORDERS=30 NALL=6 > $L/probe_pwgrid.log 2>&1
python3 gstar_probe_run.py ext CAP=5000 WALK=6 LEN=8 > $L/probe_ext.log 2>&1
python3 gstar_probe_run.py bcore CAP=5000 WALK=6 LEN=8 > $L/probe_bcore.log 2>&1
python3 gstar_run.py ext NMAX=5 MMAX=9 MAXSTATES=11000000 XCHECK=1 SHOW=0 > $L/gstarc_xcheck_ext.log 2>&1
echo ALLDONE > $L/pw_done.flag
