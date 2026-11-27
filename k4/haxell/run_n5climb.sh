#!/bin/sh
# The decisive test (k4/haxell.md §6): does the needed radius grow from n = 4 to n = 5?  Climbs at n = 5, m = 8, seeded
# from n = 4 two-move failures with a fifth agent holding a private good (results/k4_haxell/n5_seeds.txt): first with
# two moves (do two-move failures exist at n = 5?), then with three moves, for welfare (1), leximin (2), Pareto (19).
cd "$(dirname "$0")"
L=../../results/k4_haxell
i=0; head -4 $L/n5_seeds.txt | while read S; do i=$((i+1));
  for meas in 19 1 2; do
    python3 ht_wclimb.py 5 8 4 STEPS=500 CLIMBERS=2 RESTART=250 RADIUS=2 MEASURE=$meas SEED=5$i$meas START="$S" > $L/n5climb_r2_s${i}_m$meas.log 2>&1
  done
done
i=0; head -4 $L/n5_seeds.txt | while read S; do i=$((i+1));
  for meas in 19 1 2; do
    python3 ht_wclimb.py 5 8 4 STEPS=400 CLIMBERS=2 RESTART=250 RADIUS=3 MEASURE=$meas SEED=6$i$meas START="$S" > $L/n5climb_r3_s${i}_m$meas.log 2>&1
  done
done
echo ALLDONE > $L/n5climb_done.flag
