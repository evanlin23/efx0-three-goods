#!/usr/bin/env bash
# Every log of k4/rulef.md (results/k4_rulef/), one worker. Each step appends its own log; per-core checkpoints in
# $CK (default: a scratch folder) let an interrupted step resume. Usage: bash k4/rulef_runs.sh [STEP ...]
# Steps: rk (rule RK, exhaustive n <= 4 with at most three 4-good agents), feat (first-agent features and Lemma KR on
# n = 3), samp (pure n = 4 and n = 5, random profiles), hill (hill-climbing against RK), H (cores H_t), suite,
# rules (explicit rules against rule F, n = 3), check (second implementation of Lemma K), attempts.
set -u
cd "$(dirname "$0")/.."
R=results/k4_rulef; mkdir -p $R
CK=${CK:-${TMPDIR:-/tmp}/rulef_ck}; mkdir -p $CK
D=${DATA:-$CK}
steps=${*:-rk feat samp hill H suite rules check attempts}
for s in $steps; do case $s in
rk)
  python3 k4/rulef_run.py results/k4_certs_2.json.gz -A41 -r1 -D1 --data=$D/open_n2.txt > $R/rk_n2.log
  python3 k4/rulef_run.py results/k4_certs_3.json.gz -A41 -r1 -D1 --data=$D/open_n3.txt --checkpoint=$CK/rk_n3.jsonl > $R/rk_n3.log
  for f in 4_n4_1 4_n4_2 4_n4_3; do
    python3 k4/rulef_run.py results/k4_certs_$f.json.gz -A41 -r1 -D1 --data=$D/open_$f.txt --checkpoint=$CK/rk_$f.jsonl > $R/rk_n$f.log
  done ;;
feat)
  rm -f $D/idx_n3.txt
  python3 k4/rulef_run.py results/k4_certs_3.json.gz -A41 -E1 -r1 -D5 --data=$D/idx_n3.txt --checkpoint=$CK/idx_n3.jsonl > $R/rk_idx_n3.log
  python3 k4/rulef_features.py $D/idx_n3.txt > $R/features_n3.log
  grep -v "class=0" $D/idx_n3.txt > $D/k1_n3.txt
  python3 k4/rulef_rot.py $D/k1_n3.txt > $R/rotations_n3.log ;;
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
  python3 k4/rulef_H.py 1,2,3,4,5,6 --perms=5 -w0 --timeout=1800 > $R/rk_H.log ;;
suite)
  python3 k4/suite/run.py --pred=k4/rulef_suite.py:rule_rk --pred=k4/rulef_suite.py:lemma_k0 --timeout=1800 > $R/suite_rk.log ;;
rules)
  for m in 4 5 6; do
    python3 k4/rulef_run.py results/k4_certs_3.json.gz --m=$m -A40 -C3 -r1 -D6 --data=$D/rules_n3_m$m.txt --checkpoint=$CK/rules_n3_m$m.jsonl > $R/rules_n3_m$m.log
  done ;;
check)
  python3 k4/rulef_check.py $D/idx_n3.txt --max=20000 > $R/check_lemmaK_n3.log ;;
attempts)
  python3 attempts/k4_rulef_attempts.py > $R/attempts.log ;;
esac; done
