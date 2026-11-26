#!/bin/sh
# counterexample search for CONN_2 (any k) and CONN_1 (k <= 3) (k4/haxell.md §4); logs in results/k4_haxell/
cd "$(dirname "$0")"
L=../../results/k4_haxell
for m in 4 5 6 7; do for k in 3 4 $m; do
  python3 ht_climb.py sample 20000 1$m$k 2 $m $k VMAX=10 > $L/climb_sample_n2m${m}k${k}_v10.log 2>&1
  python3 ht_climb.py sample 20000 2$m$k 2 $m $k VMAX=40 > $L/climb_sample_n2m${m}k${k}_v40.log 2>&1
done; done
for m in 5 6 7; do for k in 3 4; do
  python3 ht_climb.py sample 3000 3$m$k 3 $m $k VMAX=10 > $L/climb_sample_n3m${m}k${k}_v10.log 2>&1
done; done
python3 ht_climb.py climb 200 41 2 6 4 VMAX=12 STEPS=300 > $L/climb_n2m6k4.log 2>&1
python3 ht_climb.py climb 200 42 2 6 6 VMAX=12 STEPS=300 > $L/climb_n2m6k6.log 2>&1
python3 ht_climb.py climb 200 43 2 6 3 VMAX=12 STEPS=300 > $L/climb_n2m6k3.log 2>&1
python3 ht_climb.py climb 60 44 3 6 4 VMAX=12 STEPS=150 > $L/climb_n3m6k4.log 2>&1
python3 ht_climb.py climb 60 45 3 6 3 VMAX=12 STEPS=150 > $L/climb_n3m6k3.log 2>&1
echo ALLDONE > $L/climb_done.flag
