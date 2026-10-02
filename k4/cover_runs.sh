#!/bin/sh
# Phase 2 screens of workstream compute/k4-cover: profiles with a key of def* > 0, at every f >= 1, with
# k4/cover_screen.c (k4/cover_screen_run.py, all CPUs, resumable per core). Output: results/k4_cover/screen/.
O=results/k4_cover/screen
mkdir -p $O
scr() {  # name file rand seed [extra]
  grep -q '^profiles written' $O/$1.log 2>/dev/null && return 0
  python3 k4/cover_screen_run.py $2 --rand=$3 --seed=$4 --f=1:99 $5 --out=$O/$1.jsonl.gz > $O/$1.log 2>&1
}
[ "$1" = check ] || {
scr n4_1_all results/k4_certs_4_n4_1.json.gz 0 1
scr n4_pure_r2k results/k4_certs_4_pure.json.gz 2000 2026
scr n4_3_r200k results/k4_certs_4_n4_3.json.gz 200000 2026
scr n4_pure_r200k results/k4_certs_4_pure.json.gz 200000 2027
for f in n4_1 n4_2 n4_3 n4_4 pure; do
  scr n5_${f}_r200 results/k4_certs_5_$f.json.gz 200 2026
done
scr n5_pure_bt_r200 results/k4_certs_5_pure.json.gz 200 2026 --bt=all
scr n4_2_all results/k4_certs_4_n4_2.json.gz 0 1
}
# stage 2 (run as "sh k4/cover_runs.sh check NAME PARTS"): k4/cover_check.py on the screened profiles, every f >= 1
if [ "$1" = check ]; then
  C=results/k4_cover/checks; mkdir -p $C
  i=0
  while [ $i -lt $3 ]; do
    python3 k4/cover_check.py $C/$2_p$i.jsonl.gz $O/$2.jsonl.gz --part=$i/$3 > $C/$2_p$i.log 2>&1 &
    i=$((i + 1))
  done
  wait
fi
scr n3_all results/k4_certs_3.json.gz 0 1   # run separately with --jobs=2 (see results/k4_cover/screen/n3_all.log)
