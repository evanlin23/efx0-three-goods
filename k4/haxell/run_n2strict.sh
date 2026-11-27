#!/bin/sh
# n = 2, strict-looking values (1..1000): does any state need a non-augmenting step? (ht_wclimb.py MEASURE=0: a state where no
# composite of two set moves shrinks the pool); for the n = 2 proof attempt (k4/haxell.md §6).
cd "$(dirname "$0")"
L=../../results/k4_haxell
for mk in "6 3" "7 4" "8 4" "9 5" "10 5"; do
  set -- $mk
  python3 ht_wclimb.py 2 $1 $2 STEPS=1500 CLIMBERS=2 RESTART=300 MEASURE=0 VMAX=1000 SEED=2$1$2 > $L/n2strict_aug_m$1k$2.log 2>&1
done
echo ALLDONE > $L/n2strict_done.flag
