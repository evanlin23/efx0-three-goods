#!/bin/sh
# Second implementation for the DL_R runs (k4/dl2.md §3): main's k4/c4x_check.py with separately written relation
# memberships (k4/dl2_relations_xcheck.py) on samples of the inputs (n <= 4). One process.
set -e
cd "$(dirname "$0")/.."
G=k4/suite/.cache/gapbench/results/k4_gap
R=results/k4_dl2_relations
{
python3 k4/dl2_relations_xcheck.py suite
python3 k4/dl2_relations_xcheck.py catalog $G/gap_n3.json.gz --every=5
python3 k4/dl2_relations_xcheck.py catalog $G/hard_hunt.json.gz
python3 k4/dl2_relations_xcheck.py catalog $G/gap_n4_pure_s4000.json.gz --every=40
python3 k4/dl2_relations_xcheck.py catalog $G/gap_n4_3_s4000.json.gz --every=40
} > $R/xcheck.log 2>&1
