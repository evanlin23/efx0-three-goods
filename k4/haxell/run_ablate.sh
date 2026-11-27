#!/bin/sh
# Which move kinds does W^sub need? (k4/haxell.md §6) Each kind switched off in turn (gstar_measure OFF bitmask), and the
# adversarial climb (ht_wclimb.py) looks for a state with no step; one log per (n, m, k, OFF).
cd "$(dirname "$0")"
L=../../results/k4_haxell
for off in 1 2 4 8 16 32 64; do
  for nmk in "2 7 4" "3 7 4"; do
    set -- $nmk
    [ $1 = 2 ] && [ $off = 64 ] && continue
    python3 ht_wclimb.py $1 $2 $3 STEPS=1500 CLIMBERS=3 RESTART=300 OFF=$off SEED=7$off > $L/wablate_off${off}_n$1m$2k$3.log 2>&1
  done
done
echo ALLDONE > $L/ablate_done.flag
