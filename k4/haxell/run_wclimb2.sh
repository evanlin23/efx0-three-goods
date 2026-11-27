#!/bin/sh
# Second round of W^sub climbs (ht_wclimb.py): larger k at n = 3, and n = 5; after run_wclimb.sh.
cd "$(dirname "$0")"
L=../../results/k4_haxell
while [ ! -f $L/wclimb_done.flag ]; do sleep 30; done
for nmk in "3 9 5" "3 9 6" "5 6 3" "5 7 3" "5 7 4"; do
  set -- $nmk
  python3 ht_wclimb.py $1 $2 $3 STEPS=1000 CLIMBERS=4 RESTART=300 SEED=$1$2$3 > $L/wclimb_n$1m$2k$3.log 2>&1
done
echo ALLDONE > $L/wclimb2_done.flag
