#!/bin/sh
# Phase 3 hunts of workstream compute/k4-cover (k4/cover_hunt.py), one process each, resumable (OUT.state.json).
H=results/k4_cover/hunt
mkdir -p $H
run() {  # name minutes rng seedspec...
  n=$1; mi=$2; r=$3; shift 3
  python3 k4/cover_hunt.py $H/$n.jsonl.gz --minutes=$mi --rng=$r "$@" >> $H/$n.log 2>&1
}
case "$1" in
sxx3)  run sxx3_n4_m8 $2 1 --seed='{"sets": [[0,2,4,6],[0,2,5,6],[1,3,4,7],[1,3,5,7]], "vals": [[2,3,8,4],[2,3,8,4],[2,3,8,4],[2,3,8,4]], "m": 8}' ;;
n5c)   run n5c_pathswap $2 1 --seed='{"sets": [[0,2,8,10],[1,4,9,11],[3,6,9,11],[5,7,10,11],[7,8,10,11]], "vals": [[3,4,2,8],[3,4,2,8],[4,3,2,8],[2,10,6,3],[10,2,6,3]], "m": 12}' ;;
f2x2)  run f2x2_n4_m10 $2 2 --seed='{"sets": [[0,2,4,8],[1,3,7,9],[4,5,6,7],[5,6,8,9]], "vals": [[4,2,3,8],[3,4,8,2],[3,2,4,8],[2,3,8,4]], "m": 10}' ;;
f1)    run f1_seed$3 $2 $3 --seedfile=$H/seeds_f1.jsonl.gz:$3 --frange=1:1 ;;
n6)    run n6_seed$3 $2 $3 --seedfile=$H/seeds_n6.jsonl.gz:$3 ;;
esac
case "$1" in
unc5)  run unc5_seed$3 $2 $3 --seedfile=$H/seeds_unc_n5.jsonl.gz:$3 --frange=2:99 ;;
esac
case "$1" in
f1n5)  run f1n5_seed$3 $2 $3 --seedfile=$H/seeds_f1_n5.jsonl.gz:$3 --frange=1:1 ;;
unc4)  run unc4_seed$3 $2 $3 --seedfile=$H/seeds_unc_n4.jsonl.gz:$3 --frange=2:99 ;;
esac
