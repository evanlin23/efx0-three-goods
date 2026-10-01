#!/usr/bin/env bash
# Every log of k4/rulef.md (results/k4_rulef/), one worker. Each step appends its own log; per-core checkpoints in
# $CK (default: a scratch folder) let an interrupted step resume. Usage: bash k4/rulef_runs.sh [STEP ...]
# Steps: rk (rule RK, exhaustive n <= 4 with at most three 4-good agents), featdump (n = 3 profiles where index order is
# not in K0, every first agent's classes), feat (first-agent features and Lemma KR on samples of them), samp (pure n = 4 and n = 5, random profiles), hill (hill-climbing against RK), H (cores H_t), suite,
# rules (explicit rules against rule F, n = 2 and n = 3 with m <= 5), y1 (Lemma K with kept-out sets holding goods outside R_x), n1 (as y1, and classes K0, K1 also try the run without upgrades), gap (the profiles Lemma K misses, checked against Lemma K'), check (second implementation of Lemma K), attempts, btrk (a big-top
# agent first, else RK), bigtop (a big-top agent first, else a static fallback; the failures of the fallback).
set -u
cd "$(dirname "$0")/.."
R=results/k4_rulef; mkdir -p $R
CK=${CK:-${TMPDIR:-/tmp}/rulef_ck}; mkdir -p $CK
D=${DATA:-$CK}
steps=${*:-rk featdump feat btrk bigtop samp hill H suite rules check attempts}
for s in $steps; do case $s in
rk)
  python3 k4/rulef_run.py results/k4_certs_2.json.gz -A41 -r1 -D1 --data=$D/open_n2.txt > $R/rk_n2.log
  python3 k4/rulef_run.py results/k4_certs_3.json.gz -A41 -r1 -D1 --data=$D/open_n3.txt --checkpoint=$CK/rk_n3.jsonl > $R/rk_n3.log
  for f in 4_n4_1 4_n4_2 4_n4_3; do
    python3 k4/rulef_run.py results/k4_certs_$f.json.gz -A41 -r1 -D1 --data=$D/open_$f.txt --checkpoint=$CK/rk_$f.jsonl > $R/rk_n$f.log
  done ;;
featdump)
  rm -f $D/idx_n3.txt $CK/idx_n3.jsonl
  python3 k4/rulef_run.py results/k4_certs_3.json.gz -A41 -E1 -r1 -D5 --data=$D/idx_n3.txt --checkpoint=$CK/idx_n3.jsonl > $R/rk_idx_n3.log ;;
feat)
  python3 k4/rulef_features.py $D/idx_n3.txt --every=20 > $R/features_n3.log
  grep -v "class=0" $D/idx_n3.txt > $D/k1_n3.txt
  python3 k4/rulef_rot.py $D/k1_n3.txt --every=5 > $R/rotations_n3.log ;;
btrk)
  for f in 2 3 4_n4_1 4_n4_2 4_n4_3; do
    python3 k4/rulef_run.py results/k4_certs_$f.json.gz -A42 -Q2 -r1 -D1 --data=$D/btrk_open_$f.txt --checkpoint=$CK/btrk_$f.jsonl > $R/btrk_n$f.log
  done ;;
bigtop)
  python3 k4/rulef_run.py results/k4_certs_3.json.gz -A42 -Q0 -r1 > $R/bt_n3.log
  python3 k4/rulef_run.py results/k4_certs_3.json.gz -A42 -Q1 -r1 > $R/bt1_n3.log
  python3 k4/rulef_run.py results/k4_certs_3.json.gz results/k4_certs_4_n4_1.json.gz results/k4_certs_4_n4_2.json.gz -A42 -Q3 -r1 > $R/bt3_n34.log
  python3 k4/rulef_run.py results/k4_certs_3.json.gz results/k4_certs_4_n4_1.json.gz results/k4_certs_4_n4_2.json.gz -A42 -Q4 -r1 > $R/bt4_n34.log
  python3 k4/rulef_bigtop.py results/k4_certs_3.json.gz > $R/bigtop_fallback_n3.log ;;
samp)
  python3 k4/rulef_run.py results/k4_certs_4_pure.json.gz -A41 -r1 -S20000 -D1 --data=$D/open_pure4.txt --checkpoint=$CK/rk_pure4.jsonl > $R/rk_pure4_sample.log
  for f in 5_n4_1 5_n4_2 5_n4_3 5_n4_4 5_pure; do
    python3 k4/rulef_run.py results/k4_certs_$f.json.gz -A41 -r1 -S200 -D1 --data=$D/open_$f.txt --checkpoint=$CK/rk_$f.jsonl > $R/rk_n${f}_sample.log
  done ;;
hill)
  for spec in hard4:1000:0 hard5:1000:0 deep:5000:0 grow1:1000:300 grow3:1000:200 rc7:1000:200 rc8:1000:200; do
    IFS=: read f h first <<< "$spec"
    python3 k4/rulef_run.py results/k4_lb4r_cores_$f.json.gz -A41 -r1 -H$h $( [ $first != 0 ] && echo --first=$first ) -D1 \
      --data=$D/open_hill_$f.txt --checkpoint=$CK/rk_hill_$f.jsonl > $R/rk_hill_$f.log
  done ;;
H)
  python3 k4/rulef_H.py 1,2,3,4,5 --perms=3 -w0 --timeout=900 > $R/rk_H.log ;;
suite)
  python3 k4/suite/run.py --pred=k4/rulef_suite.py:rule_rk --pred=k4/rulef_suite.py:lemma_k0 --timeout=900 > $R/suite_rk.log ;;
y1)
  python3 k4/rulef_run.py results/k4_certs_2.json.gz -A41 -r1 -Y1 > $R/rk_n2_y1.log
  python3 k4/rulef_run.py results/k4_certs_3.json.gz -A41 -r1 -Y1 --checkpoint=$CK/rk_n3_y1.jsonl > $R/rk_n3_y1.log
  for f in 4_n4_1 4_n4_2 4_n4_3; do
    python3 k4/rulef_run.py results/k4_certs_$f.json.gz -A41 -r1 -Y1 --checkpoint=$CK/rk_${f}_y1.jsonl > $R/rk_n${f}_y1.log
  done
  python3 k4/rulef_run.py results/k4_certs_4_pure.json.gz -A41 -r1 -Y1 -S2000 > $R/rk_pure4_y1_sample.log ;;
n1)
  for f in 2 3 4_n4_1 4_n4_2 4_n4_3; do
    python3 k4/rulef_run.py results/k4_certs_$f.json.gz -A41 -r1 -Y1 -N1 --checkpoint=$CK/rk_${f}_n1.jsonl > $R/rk_n${f}_n1.log
  done ;;
gap)
  for f in 4_n4_1 4_n4_2; do
    rm -f $D/gap_$f.txt $CK/gap_$f.jsonl
    python3 k4/rulef_run.py results/k4_certs_$f.json.gz -A40 -C3 -r1 -Y1 -D4 --data=$D/gap_$f.txt --checkpoint=$CK/gap_$f.jsonl > $R/gap_n$f.log
    python3 k4/rulef_gap.py $D/gap_$f.txt > $R/gap_check_n$f.log
  done ;;
rules)
  python3 k4/rulef_run.py results/k4_certs_2.json.gz -A40 -C3 -r1 > $R/rules_n2.log
  for m in 4 5; do
    python3 k4/rulef_run.py results/k4_certs_3.json.gz --m=$m -A40 -C3 -r1 -D6 --data=$D/rules_n3_m$m.txt --checkpoint=$CK/rules_n3_m$m.jsonl > $R/rules_n3_m$m.log
  done ;;
check)
  python3 k4/rulef_check.py $D/idx_n3.txt --every=200 > $R/check_lemmaK_n3.log ;;
attempts)
  python3 attempts/k4_rulef_attempts.py > $R/attempts.log ;;
esac; done
