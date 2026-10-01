#!/bin/sh
# The runs of compute/k4-dl2 (k4/dl2.c; ledger K4.STRAT.DL2, K4.STRAT.DL2E). Every log in results/k4_dl2/ starts with
# its command. EVIDENCE only. Usage: sh k4/dl2_runs.sh STEP   (from the repository root; 2 worker processes)
#   check   cross-checks of dl2.c against k4/suite/deficit_local.py and model.py (suite, catalogues, random profiles)
#   n3      every strict profile of every connected core with n <= 3
#   n4_1    every strict profile, n = 4, one 4-good agent
#   n4_2    every strict profile, n = 4, two 4-good agents (in parts, with a checkpoint)
# The catalogues are #53's files at 245040b, extracted read-only under k4/suite/.cache/gapbench (k4/strategy.md §4):
#   git archive 245040b k4 results/k4_gap results/k4_certs_2.json.gz results/k4_certs_3.json.gz \
#     results/k4_certs_4_n4_1.json.gz results/k4_certs_4_n4_2.json.gz results/k4_certs_4_n4_3.json.gz \
#     results/k4_certs_4_pure.json.gz | tar -x -C k4/suite/.cache/gapbench
set -e
C=k4/suite/.cache/gapbench/results/k4_gap
O=results/k4_dl2
mkdir -p $O
case "$1" in
check)
  python3 k4/dl2_check.py suite > $O/check_suite.log 2>&1
  for spec in "gap_n2.json.gz 1" "gap_n3.json.gz 20" "gap_n4_1.json.gz 10" "gap_n4_2_s4000.json.gz 10" \
              "gap_n4_3_s4000.json.gz 20" "gap_n4_pure_s4000.json.gz 20" "hard_hunt.json.gz 1" \
              "gap_n5_1_s100.json.gz 20" "gap_n5_2_s100.json.gz 20" "gap_n5_3_s100.json.gz 40" \
              "gap_n5_4_s100.json.gz 40" "gap_n5_pure_s100.json.gz 40"; do
    set -- $spec
    python3 k4/dl2_check.py catalog $C/$1 --every=$2 > $O/check_cat_${1%.json.gz}.log 2>&1
  done
  for spec in "k4_certs_2 200" "k4_certs_3 40" "k4_certs_4_n4_1 20" "k4_certs_4_n4_2 10" "k4_certs_4_n4_3 5" \
              "k4_certs_4_pure 5" "k4_certs_5_n4_1 1"; do
    set -- $spec
    python3 k4/dl2_check.py random results/$1.json.gz --per=$2 --seed=1 > $O/check_rand_$1.log 2>&1
  done
  ;;
n3)
  python3 k4/dl2_run.py certs results/k4_certs_2.json.gz results/k4_certs_3.json.gz --jobs=2 --rec=1000 \
    --ckpt=$O/ckpt_n3.jsonl --dump=$O/repairs_n3.jsonl.gz --tables=$O/tables_n3.json --progress > $O/n3.log 2>&1
  ;;
n4_1)
  python3 k4/dl2_run.py certs results/k4_certs_4_n4_1.json.gz --jobs=2 --rec=100 \
    --ckpt=$O/ckpt_n4_1.jsonl --dump=$O/repairs_n4_1.jsonl.gz --tables=$O/tables_n4_1.json --progress > $O/n4_1.log 2>&1
  ;;
n4_2)
  python3 k4/dl2_run.py certs results/k4_certs_4_n4_2.json.gz --jobs=2 --rec=1000 \
    --ckpt=$O/ckpt_n4_2.jsonl --dump=$O/repairs_n4_2.jsonl.gz --tables=$O/tables_n4_2.json --progress > $O/n4_2.log 2>&1
  ;;
*) echo "usage: sh k4/dl2_runs.sh check|n3|n4_1|n4_2"; exit 2 ;;
esac
