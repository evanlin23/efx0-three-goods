#!/bin/sh
# New n = 5 samples for workstream compute/k4-zmove (k4/cover_screen_run.py, resumable per core): profiles with a key of
# def* > 0 at any f >= 1, written to results/k4_zmove/screen/ for k4/zmove_runs.sh n5. Seeds differ from compute/k4-cover's.
O=results/k4_zmove/screen
mkdir -p $O
scr() {  # name file rand seed [extra]
  grep -q '^profiles written' $O/$1.log 2>/dev/null && return 0
  $NICE python3 k4/cover_screen_run.py $2 --rand=$3 --seed=$4 --f=1:99 --jobs=${J:-2} $5 --out=$O/$1.jsonl.gz > $O/$1.log 2>&1
}
[ -n "$1" ] || {
scr n5_n4_3_r500 results/k4_certs_5_n4_3.json.gz 500 4041
scr n5_n4_4_r500 results/k4_certs_5_n4_4.json.gz 500 4041
scr n5_pure_r500 results/k4_certs_5_pure.json.gz 500 4041
scr n5_pure_bt_r500 results/k4_certs_5_pure.json.gz 500 4041 --bt=all
scr n5_n4_1_r2k results/k4_certs_5_n4_1.json.gz 2000 4041
scr n5_n4_2_r2k results/k4_certs_5_n4_2.json.gz 2000 4041
}
# larger big-top n = 5 samples (the big-top types carry most keys with def* > 0)
[ "$1" = bt ] && {
scr n5_pure_bt_r3k results/k4_certs_5_pure.json.gz 3000 5051 --bt=all
scr n5_n4_4_bt_r1k results/k4_certs_5_n4_4.json.gz 1000 5051 --bt=all
scr n5_n4_3_bt_r1k results/k4_certs_5_n4_3.json.gz 1000 5051 --bt=all
}
# every strict profile of every n = 4 core with two 4-good agents (low priority; resumable per core)
[ "$1" = n4_2 ] && J=1 NICE="nice -n 10" scr n4_2_all results/k4_certs_4_n4_2.json.gz 0 1
