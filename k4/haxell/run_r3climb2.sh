#!/bin/sh
# Longer three-move climbs from every known two-move failure seed (after run_r3climb.sh), welfare and leximin.
cd "$(dirname "$0")"
L=../../results/k4_haxell
while [ ! -f $L/r3climb_done.flag ]; do sleep 30; done
grep -h "^COUNTEREXAMPLE" $L/lclimb_seed*_n4m7k4.log | sed 's/^COUNTEREXAMPLE //; s/ |.*//' > $L/ls4_seeds_all.txt
i=0; cat $L/ls4_seeds_all.txt $L/ws4_seeds.txt | head -8 | while read S; do i=$((i+1)); for meas in 1 2; do
  python3 ht_wclimb.py 4 7 4 STEPS=2500 CLIMBERS=2 RESTART=600 RADIUS=3 MEASURE=$meas SEED=4$i$meas START="$S" > $L/r3climb2_s${i}_m$meas.log 2>&1
done; done
echo ALLDONE > $L/r3climb2_done.flag
