#!/bin/sh
# DL_R runs of k4/dl2.md §3 (results/k4_dl2_relations/). Needs #53's catalogues at 245040b in
# k4/suite/.cache/gapbench (the git archive command of k4/strategy.md §4). Two worker processes (J=1 for one).
set -e
cd "$(dirname "$0")/.."
G=k4/suite/.cache/gapbench/results/k4_gap
R=results/k4_dl2_relations
mkdir -p $R
python3 k4/dl2_relations.py suite > $R/suite.log 2>&1
for spec in "gap_n2 1" "gap_n3 1" "gap_n4_1 10" "gap_n4_2_s4000 10" "gap_n4_3_s4000 10" "gap_n4_pure_s4000 10" \
            "hard_hunt 1" "gap_n5_1_s100 20" "gap_n5_2_s100 20" "gap_n5_3_s100 20" "gap_n5_4_s100 20" "gap_n5_pure_s100 20" \
            "hunt_n4_2_all 1" "hunt_n4_3_s400k 1" "hunt_n4_pure_s400k 1" "hunt_n5_3_s2000 1" "hunt_n5_4_s2000 1" "hunt_n5_pure_s2000 1"; do
  set -- $spec
  python3 k4/dl2_relations.py catalog $G/$1.json.gz --every=$2 --jobs=${J:-2} --out=$R/$1_e$2.jsonl.gz > $R/$1_e$2.log 2>&1
done
