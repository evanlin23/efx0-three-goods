#!/bin/sh
# Three-move forms of the set-move lemma (k4/haxell.md §6): climbs (ht_wclimb.py RADIUS=3) for a state with no step
# within three moves, welfare (MEASURE=1) and leximin (MEASURE=2), from the known two-move failures and from random starts.
cd "$(dirname "$0")"
L=../../results/k4_haxell
W=$(head -1 $L/ws4_seeds.txt); X=$(head -1 $L/ls4_seed.txt)
for meas in 1 2; do
  python3 ht_wclimb.py 4 7 4 STEPS=800 CLIMBERS=2 RESTART=300 RADIUS=3 MEASURE=$meas SEED=31$meas START="$W" > $L/r3climb_m${meas}_wseed_n4m7k4.log 2>&1
  python3 ht_wclimb.py 4 7 4 STEPS=800 CLIMBERS=2 RESTART=300 RADIUS=3 MEASURE=$meas SEED=32$meas START="$X" > $L/r3climb_m${meas}_lseed_n4m7k4.log 2>&1
done
for nmk in "4 7 4" "4 8 4" "5 7 4"; do
  set -- $nmk
  for meas in 1 2; do
    python3 ht_wclimb.py $1 $2 $3 STEPS=800 CLIMBERS=2 RESTART=300 RADIUS=3 MEASURE=$meas SEED=33$1$2$meas > $L/r3climb_m${meas}_n$1m$2k$3.log 2>&1
  done
done
echo ALLDONE > $L/r3climb_done.flag
