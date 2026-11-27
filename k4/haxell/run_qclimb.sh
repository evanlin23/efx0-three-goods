#!/bin/sh
# Measure Q (gstar_measure measure 20, k4/haxell.md §6): a Pareto step within two moves, or a smaller pool within three.
# Q holds at all 44 known two-move failures (rescue_anatomy.log) and implies P^sub_3.  Climbs that try to break it: seeded
# from the four n = 4 seeds of the Pareto climbs and the n = 5 failure, then random at n = 4, 5.
cd "$(dirname "$0")"
L=../../results/k4_haxell
i=0; cat $L/ws4_seeds.txt $L/ls4_seeds_all.txt 2>/dev/null | head -4 | while read S; do i=$((i+1));
  python3 ht_wclimb.py 4 7 4 STEPS=3000 CLIMBERS=2 RESTART=500 RADIUS=3 MEASURE=20 SEED=20$i START="$S" > $L/qclimb_seed${i}_n4m7k4.log 2>&1; done
S5=$(grep '^COUNTEREXAMPLE' $L/n5climb_r2_s4_m19.log | head -1 | sed 's/^COUNTEREXAMPLE //; s/ |.*//')
python3 ht_wclimb.py 5 8 4 STEPS=800 CLIMBERS=2 RESTART=300 RADIUS=3 MEASURE=20 SEED=205 START="$S5" > $L/qclimb_n5seed_n5m8k4.log 2>&1
for nmk in "4 7 4 2500" "4 8 4 1500" "5 7 4 1200" "5 8 4 600"; do
  set -- $nmk
  python3 ht_wclimb.py $1 $2 $3 STEPS=$4 CLIMBERS=2 RESTART=400 RADIUS=3 MEASURE=20 SEED=21$1$2 > $L/qclimb_n$1m$2k$3.log 2>&1
done
echo ALLDONE > $L/qclimb_done.flag
