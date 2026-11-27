#!/bin/sh
# Does the needed radius grow at n = 6?  Climbs at n = 6, m = 8, seeded from n = 4 two-move failures with two more agents
# sharing one new good (results/k4_haxell/n6_seeds.txt): two moves, then three, for Pareto (19) and welfare (1).
cd "$(dirname "$0")"
L=../../results/k4_haxell
i=0; head -2 $L/n6_seeds.txt | while read S; do i=$((i+1));
  for meas in 19 1; do
    python3 ht_wclimb.py 6 8 4 STEPS=250 CLIMBERS=2 RESTART=150 RADIUS=2 MEASURE=$meas SEED=7$i$meas START="$S" > $L/n6climb_r2_s${i}_m$meas.log 2>&1
    python3 ht_wclimb.py 6 8 4 STEPS=250 CLIMBERS=2 RESTART=150 RADIUS=3 MEASURE=$meas SEED=8$i$meas START="$S" > $L/n6climb_r3_s${i}_m$meas.log 2>&1
  done
done
echo ALLDONE > $L/n6climb_done.flag
