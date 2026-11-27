#!/bin/sh
# W^sub with welfare (phi1) and with leximin (phi2) together (gstar_measure ... ONLY 1, ONLY2 2) on the exhaustive n = 3
# value grids (ht_n3grid.py); W^sub with welfare is refuted at n = 4 (k4/haxell.md §6), so leximin is the candidate.
cd "$(dirname "$0")"
L=../../results/k4_haxell
M=2,1,1,1,0,0,0,2
for m in 2 3 4 5 6 7; do python3 ht_n3grid.py K=3 MMIN=$m MMAX=$m VALS=1,2,4,7,12 MARGS=$M >> $L/n3grid_wl_k3_v12.log 2>&1; done
for m in 2 3 4 5; do python3 ht_n3grid.py K=4 MMIN=$m MMAX=$m VALS=1,2,4,7 MARGS=$M >> $L/n3grid_wl_k4_v7.log 2>&1; done
for m in 6 7; do python3 ht_n3grid.py K=4 MMIN=$m MMAX=$m VALS=1,2,4 MARGS=$M >> $L/n3grid_wl_k4_v4.log 2>&1; done
for m in 8 9; do python3 ht_n3grid.py K=3 MMIN=$m MMAX=$m VALS=1,2,4,7,12 MARGS=$M >> $L/n3grid_wl_k3_v12.log 2>&1; done
echo ALLDONE > $L/n3grid_wl_done.flag
