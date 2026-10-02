#!/usr/bin/env bash
# Every run of results/k4_rulef_hunt/ (workstream compute/k4-lemmam-hunt): the hunt for a counterexample to Lemma M.
# Each step appends to its own log and resumes from its own checkpoint results/k4_rulef_hunt/ck/RUN.jsonl (rerun the
# same step after an interruption). Usage: bash k4/rulef_hunt_runs.sh STEP [STEP ...]
# Classes: Lemma K with Remark 4's kept-out sets (-Y1), K1 with Lemma K's slot count at the rotated state (-T1, the
# evaluator's default; rulef.c's k1_run gives a rotated agent no slot, see k4/rulef_hunt_eval.c). n5hi_cK1 (partial,
# 1,281 cores) was run with -T0 (rulef.c's K1) before that difference was found: results/k4_rulef_hunt/n5hi_cK1.log.
#   n5hi    n = 5 cores with three, four or five 4-good agents and m >= 9: 20,000 evaluations each, key M
#   n5lo    the same classes with m <= 8: 4,000 each;   n5n12   n = 5 with one or two 4-good agents: 6,000 each
#   seedsH  H_1 under all 120 agent orders, H_2 under 8 relabelings: 60,000 each, starting at H_t's own profile
#   suite   the suite's strict k = 4 core instances with 4 <= n <= 9: 60,000 each, starting at the instance
#   n4pure  n = 4 with four 4-good agents (the class only sampled before): 500,000 each
#   deep5   the exhaustive two-change descent (all profiles differing in one or two agents' types, repeated while the
#           key improves), then all agent orders of the result (--relabel): from the best tight profile (nwork <= 1)
#           of every core (deep5t) and from every best profile with nwork <= 2 (deep5x; n = 5 runs, suite, n4pure); climbs with key R and
#           kicks from every best profile with nwork <= 3 (200,000 each, agent orders scanned after each restart; deep5r)
#   pure2   a second pass over the n = 5 pure cores with 9 <= m <= 11 (where n5hi's tight profiles are): another seed,
#           60,000 each, agent orders scanned after each restart (--relabel)
#   deep5t2 as deep5t, from the best tight profile of every core (and relabeled core) in pure2 and deep5r
#   n6      n = 6 (one 4-good agent; the only n = 6 certificate file): m >= 10: 10,000 each with agent orders scanned
#           (--relabel), m <= 9: 2,000 each
#   deep6   the exhaustive two-change descent from every n = 6 best profile with nwork <= 5
#   check   the profiles with nwork <= 1 against the second implementation (k4/rulef_hunt_check.py)
set -u
cd "$(dirname "$0")/.."
R=results/k4_rulef_hunt; mkdir -p $R/ck
C=results
H="python3 k4/rulef_hunt.py"
for s in "$@"; do case $s in
n5hi)
  $H n5hi --file=$C/k4_certs_5_n4_3.json.gz --file=$C/k4_certs_5_n4_4.json.gz --file=$C/k4_certs_5_pure.json.gz \
     --mmin=9 --evals=20000 --key=M >> $R/n5hi.log 2>&1 ;;
n5lo)
  $H n5lo --file=$C/k4_certs_5_n4_3.json.gz --file=$C/k4_certs_5_n4_4.json.gz --file=$C/k4_certs_5_pure.json.gz \
     --mmax=8 --evals=4000 --key=M >> $R/n5lo.log 2>&1 ;;
n5n12)
  $H n5n12 --file=$C/k4_certs_5_n4_1.json.gz --file=$C/k4_certs_5_n4_2.json.gz --evals=6000 --key=M >> $R/n5n12.log 2>&1 ;;
seedsH)
  [ -f $R/seeds_H.jsonl ] || python3 k4/rulef_hunt_seeds.py H $R/seeds_H.jsonl
  $H seedsH --seeds=$R/seeds_H.jsonl --evals=60000 --key=M >> $R/seedsH.log 2>&1 ;;
suite)
  [ -f $R/seeds_suite.jsonl ] || python3 k4/rulef_hunt_seeds.py suite $R/seeds_suite.jsonl
  $H suite --seeds=$R/seeds_suite.jsonl --evals=60000 --key=M >> $R/suite.log 2>&1 ;;
n4pure)
  $H n4pure --file=$C/k4_certs_4_pure.json.gz --evals=500000 --key=M >> $R/n4pure.log 2>&1 ;;
deep5)
  python3 k4/rulef_hunt_seeds.py tight $R/seeds_tight5.jsonl $R/tight_n5hi.jsonl.gz $(ls $R/tight_n5lo.jsonl.gz $R/tight_n5n12.jsonl.gz \
     $R/tight_seedsH.jsonl.gz $R/tight_suite.jsonl.gz 2>/dev/null)
  python3 k4/rulef_hunt_seeds.py best $R/seeds_deep5x.jsonl 2 $R/ck/n5hi.jsonl $R/ck/n5lo.jsonl $R/ck/n5n12.jsonl \
     $R/ck/seedsH.jsonl $R/ck/suite.jsonl $R/ck/n4pure.jsonl
  python3 k4/rulef_hunt_seeds.py best $R/seeds_deep5r.jsonl 3 $R/ck/n5hi.jsonl $R/ck/n5lo.jsonl $R/ck/n5n12.jsonl \
     $R/ck/seedsH.jsonl $R/ck/suite.jsonl
  $H deep5t --seeds=$R/seeds_tight5.jsonl --exhaust --relabel --evals=8000000 --key=M >> $R/deep5t.log 2>&1
  $H deep5x --seeds=$R/seeds_deep5x.jsonl --exhaust --relabel --evals=3000000 --key=M >> $R/deep5x.log 2>&1
  $H deep5r --seeds=$R/seeds_deep5r.jsonl --evals=200000 --key=R --kick=0.7 --relabel >> $R/deep5r.log 2>&1 ;;
pure2)
  $H pure2 --file=$C/k4_certs_5_pure.json.gz --mmin=9 --mmax=11 --evals=60000 --key=M --seed=2 --relabel >> $R/pure2.log 2>&1 ;;
n6)
  $H n6hi --file=$C/k4_certs_6_n4_1.json.gz --mmin=10 --evals=10000 --key=M --relabel >> $R/n6hi.log 2>&1
  $H n6lo --file=$C/k4_certs_6_n4_1.json.gz --mmax=9 --evals=2000 --key=M >> $R/n6lo.log 2>&1 ;;
deep6)
  [ -f $R/seeds_deep6.jsonl ] || python3 k4/rulef_hunt_seeds.py best $R/seeds_deep6.jsonl 5 $R/ck/n6hi.jsonl $R/ck/n6lo.jsonl
  $H deep6x --seeds=$R/seeds_deep6.jsonl --exhaust --evals=3000000 --key=M >> $R/deep6x.log 2>&1 ;;
deep5t2)
  python3 k4/rulef_hunt_seeds.py tight $R/seeds_tight5b.jsonl $R/tight_pure2.jsonl.gz $R/tight_deep5r.jsonl.gz
  $H deep5t2 --seeds=$R/seeds_tight5b.jsonl --exhaust --relabel --evals=8000000 --key=M >> $R/deep5t2.log 2>&1 ;;
check)
  ls $R/tight_*.jsonl.gz >/dev/null 2>&1 && python3 k4/rulef_hunt_check.py $R/tight_*.jsonl.gz > $R/check.log 2>&1 ;;
*) echo "unknown step $s"; exit 1 ;;
esac; done
