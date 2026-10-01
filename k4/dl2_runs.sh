#!/bin/sh
# The DL2 classification runs of k4/dl2.md (results/k4_dl2_classify/). Needs #53's catalogues at 245040b in
# k4/suite/.cache/gapbench (the git archive command of k4/strategy.md §4). Two worker processes.
set -e
cd "$(dirname "$0")/.."
G=k4/suite/.cache/gapbench/results/k4_gap
R=results/k4_dl2_classify
mkdir -p $R
python3 k4/dl2_classify.py suite --out=$R/suite.jsonl.gz > $R/suite.log 2>&1
for spec in "gap_n2 1" "gap_n3 1" "gap_n4_1 10" "gap_n4_2_s4000 10" "gap_n4_3_s4000 10" "gap_n4_pure_s4000 10" \
            "hard_hunt 1" "gap_n5_1_s100 20" "gap_n5_2_s100 20" "gap_n5_3_s100 20" "gap_n5_4_s100 20" "gap_n5_pure_s100 20"; do
  set -- $spec
  python3 k4/dl2_classify.py catalog $G/$1.json.gz --every=$2 --jobs=2 --out=$R/$1_e$2.jsonl.gz > $R/$1_e$2.log 2>&1
done
python3 k4/dl2_table.py $R/*.jsonl.gz > $R/table.md
