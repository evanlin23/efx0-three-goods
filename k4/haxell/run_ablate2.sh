#!/bin/sh
# W^sub with the two move kinds the single ablations did not need switched off together (OFF = 1 + 8: no swaps of two
# agents' goods, no transfers of two or more pooled goods); ht_wclimb.py looks for a state with no step.
cd "$(dirname "$0")"
L=../../results/k4_haxell
for nmk in "2 7 4" "2 8 4" "3 7 4" "3 8 4" "4 7 4"; do
  set -- $nmk
  python3 ht_wclimb.py $1 $2 $3 STEPS=1500 CLIMBERS=3 RESTART=300 OFF=9 SEED=9$1$2 > $L/wablate_off9_n$1m$2k$3.log 2>&1
done
echo ALLDONE > $L/ablate2_done.flag
