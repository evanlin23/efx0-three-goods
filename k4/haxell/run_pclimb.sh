#!/bin/sh
# The Pareto form of the set-move lemma (k4/haxell.md §6): three-move climbs (P^sub_3) at n = 4, 5, seeded and random,
# and two-move climbs (P^sub) at k = 3 for n = 4, 5 (are four-good agents needed for a failure?).
cd "$(dirname "$0")"
L=../../results/k4_haxell
i=0; cat $L/ws4_seeds.txt $L/ls4_seeds_all.txt 2>/dev/null | head -4 | while read S; do i=$((i+1));
  python3 ht_wclimb.py 4 7 4 STEPS=1200 CLIMBERS=2 RESTART=400 RADIUS=3 MEASURE=19 SEED=8$i START="$S" > $L/p3climb_seed${i}_n4m7k4.log 2>&1; done
for nmk in "5 7 4" "4 8 4" "5 8 4"; do
  set -- $nmk
  python3 ht_wclimb.py $1 $2 $3 STEPS=600 CLIMBERS=2 RESTART=300 RADIUS=3 MEASURE=19 SEED=9$1$2 > $L/p3climb_n$1m$2k$3.log 2>&1
done
for nmk in "4 7 3" "4 8 3" "5 7 3"; do
  set -- $nmk
  python3 ht_wclimb.py $1 $2 $3 STEPS=1500 CLIMBERS=2 RESTART=400 RADIUS=2 MEASURE=19 SEED=7$1$2 > $L/p2climb_n$1m$2k$3.log 2>&1
done
echo ALLDONE > $L/pclimb_done.flag
