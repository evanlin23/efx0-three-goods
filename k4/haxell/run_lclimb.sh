#!/bin/sh
# Adversarial climbs for a counterexample to W^sub with leximin (ht_wclimb.py MEASURE=2): random starts, and starts at
# the 36 instances where W^sub with welfare fails (results/k4_haxell/wclimb_tight_n4m7k4.log).
cd "$(dirname "$0")"
L=../../results/k4_haxell
grep "^COUNTEREXAMPLE" $L/wclimb_tight_n4m7k4.log | sed 's/^COUNTEREXAMPLE //; s/ |.*//' | head -6 > $L/ws4_seeds.txt
i=0; while read S; do i=$((i+1)); python3 ht_wclimb.py 4 7 4 STEPS=1500 CLIMBERS=2 RESTART=400 MEASURE=2 SEED=5$i START="$S" > $L/lclimb_seed${i}_n4m7k4.log 2>&1; done < $L/ws4_seeds.txt
for nmk in "4 7 4" "3 8 4" "4 8 4" "5 7 4" "2 9 5"; do
  set -- $nmk
  python3 ht_wclimb.py $1 $2 $3 STEPS=2000 CLIMBERS=3 RESTART=400 MEASURE=2 SEED=6$1$2$3 > $L/lclimb_n$1m$2k$3.log 2>&1
done
echo ALLDONE > $L/lclimb_done.flag
