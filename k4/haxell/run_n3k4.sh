#!/bin/sh
# P^sub (two set moves, Pareto) at n = 3 with an agent valuing four goods, over strict type profiles (ht_n3types.py):
# every orbit for m = 4, random profiles per shape for m = 5..8.  Starts when the strict-domain core pass is done.
cd "$(dirname "$0")"
L=../../results/k4_haxell
while [ ! -f $L/p3strict_done.flag ]; do sleep 60; done
python3 ht_n3types.py K=4 MMIN=4 MMAX=4 NEED4=1 PROCS=2 > $L/n3types_k4_m4.log 2>&1
python3 ht_n3types.py K=4 MMIN=5 MMAX=6 NEED4=1 SAMPLE=2000 SEED=31 PROCS=2 > $L/n3types_k4_m56_sample.log 2>&1
python3 ht_n3types.py K=4 MMIN=7 MMAX=8 NEED4=1 SAMPLE=500 SEED=32 PROCS=2 > $L/n3types_k4_m78_sample.log 2>&1
echo ALLDONE > $L/n3k4_done.flag
