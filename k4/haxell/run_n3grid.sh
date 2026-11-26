#!/bin/sh
# W^sub (k4/haxell.md §6) on exhaustive n = 3 value grids (ht_n3grid.py): every shape and every value assignment up to
# isomorphism, every partial EFX0 state with a nonempty pool; one log per grid, one section per m.
cd "$(dirname "$0")"
L=../../results/k4_haxell
cc -O2 -o gstar_measure gstar_measure.c
for m in 2 3 4 5 6 7 8 9; do python3 ht_n3grid.py K=3 MMIN=$m MMAX=$m VALS=1,2,4,7,12 MARGS=2,1,1,1 >> $L/n3grid_k3_v12.log 2>&1; done
for m in 2 3 4 5; do python3 ht_n3grid.py K=4 MMIN=$m MMAX=$m VALS=1,2,4,7 MARGS=2,1,1,1 >> $L/n3grid_k4_v7.log 2>&1; done
for m in 6 7 8; do python3 ht_n3grid.py K=4 MMIN=$m MMAX=$m VALS=1,2,4 MARGS=2,1,1,1 >> $L/n3grid_k4_v4.log 2>&1; done
echo ALLDONE > $L/n3grid_done.flag
