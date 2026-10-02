#!/bin/sh
# Phase 2, second round of screens (compute/k4-cover): larger n = 5 samples, after k4/cover_runs.sh.
O=results/k4_cover/screen
scr() {  # name file rand seed [extra]
  grep -q '^profiles written' $O/$1.log 2>/dev/null && return 0
  python3 k4/cover_screen_run.py $2 --rand=$3 --seed=$4 --f=1:99 $5 --out=$O/$1.jsonl.gz > $O/$1.log 2>&1
}
scr n5_n4_4_r2k results/k4_certs_5_n4_4.json.gz 2000 3031
scr n5_pure_r2k results/k4_certs_5_pure.json.gz 2000 3031
scr n5_pure_bt_r2k results/k4_certs_5_pure.json.gz 2000 3031 --bt=all
