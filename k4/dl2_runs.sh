#!/bin/sh
# The runs of compute/k4-dl2 (k4/dl2.c; ledger K4.DL2.KN, K4.DL2.SHAPE). Every log in results/k4_dl2/ starts with
# its command. EVIDENCE only. Usage: sh k4/dl2_runs.sh STEP   (from the repository root; 2 worker processes)
#   check   cross-checks of dl2.c against k4/suite/deficit_local.py and model.py (suite, catalogues, random profiles)
#   n3      every strict profile of every connected k = 4 core with n <= 3 and a 4-good agent (K4.R3's lists)
#   n4_1    every strict profile, n = 4, one 4-good agent
#   n4_2    every strict profile, n = 4, two 4-good agents (with a checkpoint)
#   n4rand P  P random strict profiles of every n = 4 core with three or four 4-good agents
#   n4cat   every record of #53's n = 4 catalogues with three or four 4-good agents and of its n = 4 hunts
#   n5cat   every record of #53's n = 5 gap catalogues and hunts (f >= 1 gap profiles)
#   n5rand P  P random strict profiles of every n = 5 core of the certificate files (connected, a 4-good agent)
#   n6rand P CORES  P random strict profiles of every n = 6 core with one 4-good agent, and of CORES random n = 6 cores
#   cycle N [P]  the cyclic cores of k4/dl2_cycle.py (the f = 0 rotation trap generalized to n = N), every profile
#           with the cyclic order of top and second goods, or P random ones per core
#   ht P    H_2 of k4/c4.md §7 with §7's values and P random strict profiles of it;  h3: H_3 with §7's values
# Dumps (repairs_*.jsonl.gz): every profile with k* >= 3, a sample of k* = 1 and k* = 2 (rates in each command).
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
  python3 k4/dl2_run.py certs results/k4_certs_2.json.gz results/k4_certs_3.json.gz --jobs=2 --rec=10000 --rec2=100 \
    --ckpt=$O/ckpt_n3.jsonl --dump=$O/repairs_n3.jsonl.gz --tables=$O/tables_n3.json --progress > $O/n3.log 2>&1
  ;;
n4_1)
  python3 k4/dl2_run.py certs results/k4_certs_4_n4_1.json.gz --jobs=2 --rec=100 --rec2=1 \
    --ckpt=$O/ckpt_n4_1.jsonl --dump=$O/repairs_n4_1.jsonl.gz --tables=$O/tables_n4_1.json --progress > $O/n4_1.log 2>&1
  ;;
n4_2)
  python3 k4/dl2_run.py certs results/k4_certs_4_n4_2.json.gz --jobs=2 --rec=1000 --rec2=20 \
    --ckpt=$O/ckpt_n4_2.jsonl --dump=$O/repairs_n4_2.jsonl.gz --tables=$O/tables_n4_2.json --progress > $O/n4_2.log 2>&1
  ;;
n4rand)
  for f in k4_certs_4_n4_3 k4_certs_4_pure; do
    python3 k4/dl2_run.py certs results/$f.json.gz --sample=$2 --seed=1 --jobs=2 --rec=0 --rec2=20 \
      --ckpt=$O/ckpt_n4rand.jsonl --dump=$O/repairs_n4rand.jsonl.gz --tables=$O/tables_n4rand_$f.json > $O/n4rand_$f.log 2>&1
  done
  ;;
n4cat)
  for f in gap_n4_3_s4000 gap_n4_pure_s4000 hunt_n4_2_all hunt_n4_3_s400k hunt_n4_pure_s400k; do
    python3 k4/dl2_run.py catalog $C/$f.json.gz --jobs=2 --rec=500 --rec2=5 \
      --dump=$O/repairs_n4cat.jsonl.gz --tables=$O/tables_n4cat_$f.json > $O/n4cat_$f.log 2>&1
  done
  ;;
n5cat)
  for f in gap_n5_1_s100 gap_n5_2_s100 gap_n5_3_s100 gap_n5_4_s100 gap_n5_pure_s100 hunt_n5_3_s2000 hunt_n5_4_s2000 hunt_n5_pure_s2000; do
    python3 k4/dl2_run.py catalog $C/$f.json.gz --jobs=2 --rec=500 --rec2=5 \
      --dump=$O/repairs_n5cat.jsonl.gz --tables=$O/tables_n5cat_$f.json > $O/n5cat_$f.log 2>&1
  done
  ;;
n5rand)
  for f in k4_certs_5_n4_1 k4_certs_5_n4_2 k4_certs_5_n4_3 k4_certs_5_n4_4 k4_certs_5_pure; do
    python3 k4/dl2_run.py certs results/$f.json.gz --sample=$2 --seed=1 --jobs=2 --rec=0 --rec2=20 \
      --ckpt=$O/ckpt_n5rand.jsonl --dump=$O/repairs_n5rand.jsonl.gz --tables=$O/tables_n5rand_$f.json > $O/n5rand_$f.log 2>&1
  done
  ;;
n6rand)
  python3 k4/dl2_run.py certs results/k4_certs_6_n4_1.json.gz --sample=$2 --seed=1 --jobs=2 --rec=0 --rec2=20 \
    --ckpt=$O/ckpt_n6rand.jsonl --dump=$O/repairs_n6rand.jsonl.gz --tables=$O/tables_n6rand_n4_1.json > $O/n6rand_n4_1.log 2>&1
  [ -f $O/randcores_6.json.gz ] || python3 k4/lb4_randcores.py 6 $3 $O/randcores_6.json.gz --seed=6 > $O/randcores_6.log 2>&1
  python3 k4/dl2_run.py certs $O/randcores_6.json.gz --sample=$2 --seed=1 --jobs=2 --rec=0 --rec2=20 \
    --ckpt=$O/ckpt_n6rand.jsonl --dump=$O/repairs_n6rand.jsonl.gz --tables=$O/tables_n6rand_random.json > $O/n6rand_random.log 2>&1
  ;;
ht)
  python3 k4/dl2_run.py ht 2 --rec=1 --dump=$O/repairs_ht.jsonl.gz --tables=$O/tables_h2.json > $O/h2.log 2>&1
  python3 k4/dl2_run.py ht 2 --sample=$2 --seed=1 --rec=0 --rec2=1 --dump=$O/repairs_ht.jsonl.gz --tables=$O/tables_h2_rand.json > $O/h2_rand.log 2>&1
  ;;
cycle)
  python3 k4/dl2_cycle.py $2 --jobs=2 ${3:+--sample=$3} --dump=$O/repairs_cycle.jsonl.gz \
    --tables=$O/tables_cycle_n$2.json > $O/cycle_n$2.log 2>&1
  ;;
h3)
  python3 k4/dl2_run.py ht 3 --wide --rec=1 --dump=$O/repairs_ht.jsonl.gz --tables=$O/tables_h3.json > $O/h3.log 2>&1
  ;;
*) echo "usage: sh k4/dl2_runs.sh check|n3|n4_1|n4_2|n4rand P|n4cat|n5cat|n5rand P|n6rand P CORES|cycle N [P]|ht P|h3"; exit 2 ;;
esac
