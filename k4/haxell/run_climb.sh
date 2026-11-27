#!/bin/sh
# counterexample search for CONN_2 (any k) and CONN_1 (k <= 3) (k4/haxell.md §4), Python census; logs in
# results/k4_haxell/.  Only the n = 2, m <= 6 samples below were run with this script; the Python census is too slow
# at m >= 7, and the larger samples went through the C census instead (run_sample_c.sh).  The hill climbs of
# ht_climb.py (mode climb) were not run.
cd "$(dirname "$0")"
L=../../results/k4_haxell
for m in 4 5 6; do for k in 3 4 $m; do
  python3 ht_climb.py sample 20000 1$m$k 2 $m $k VMAX=10 > $L/climb_sample_n2m${m}k${k}_v10.log 2>&1
  python3 ht_climb.py sample 20000 2$m$k 2 $m $k VMAX=40 > $L/climb_sample_n2m${m}k${k}_v40.log 2>&1
done; done
