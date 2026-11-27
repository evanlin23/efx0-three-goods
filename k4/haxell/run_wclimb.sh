#!/bin/sh
# Adversarial hill-climbing for a W^sub counterexample (ht_wclimb.py, k4/haxell.md §6); one log per (n, m, k).
cd "$(dirname "$0")"
L=../../results/k4_haxell
python3 ht_wclimb.py 2 7 4 STEPS=600 CLIMBERS=3 SUB=0 RESTART=200 > $L/wclimb_W_n2m7k4.log 2>&1      # validation: finds W's failures
for nmk in "2 7 4" "2 8 4" "2 9 5" "2 10 5" "2 10 6" "3 6 3" "3 7 3" "3 7 4" "3 8 4" "3 8 5" "4 6 3" "4 7 3" "4 7 4" "4 8 4"; do
  set -- $nmk
  python3 ht_wclimb.py $1 $2 $3 STEPS=3000 CLIMBERS=4 RESTART=400 SEED=$1$2$3 > $L/wclimb_n$1m$2k$3.log 2>&1
done
echo ALLDONE > $L/wclimb_done.flag
