#!/bin/sh
# T1-stuck states of DL13 on #53's catalogues (k4/dl13.md §1). One worker, sequential; about an hour.
# Needs the catalogues at 245040b in k4/suite/.cache/gapbench (k4/strategy.md §4).
set -e
G=k4/suite/.cache/gapbench/results/k4_gap
R=results/k4_dl13
mkdir -p $R
python3 k4/dl13_stuck.py suite --out=$R/stuck_suite.jsonl.gz > $R/stuck_suite.log
python3 k4/dl13_stuck.py catalog $G/gap_n3.json.gz --out=$R/stuck_gap_n3.jsonl.gz > $R/stuck_gap_n3.log
python3 k4/dl13_stuck.py catalog $G/hard_hunt.json.gz --out=$R/stuck_hard_hunt.jsonl.gz > $R/stuck_hard_hunt.log
for c in gap_n4_1 gap_n4_2_s4000 gap_n4_3_s4000 gap_n4_pure_s4000; do
  python3 k4/dl13_stuck.py catalog $G/$c.json.gz --every=4 --out=$R/stuck_${c}_e4.jsonl.gz > $R/stuck_${c}_e4.log
  python3 k4/dl13_stuck.py catalog $G/$c.json.gz --fmin=2 --out=$R/stuck_${c}_f2.jsonl.gz > $R/stuck_${c}_f2.log
done
for c in hunt_n4_2_all hunt_n4_3_s400k hunt_n4_pure_s400k; do
  python3 k4/dl13_stuck.py catalog $G/$c.json.gz --every=10 --out=$R/stuck_${c}_e10.jsonl.gz > $R/stuck_${c}_e10.log
done
for c in gap_n5_1_s100 gap_n5_2_s100 gap_n5_3_s100 gap_n5_4_s100 gap_n5_pure_s100; do
  python3 k4/dl13_stuck.py catalog $G/$c.json.gz --every=20 --out=$R/stuck_${c}_e20.jsonl.gz > $R/stuck_${c}_e20.log
  python3 k4/dl13_stuck.py catalog $G/$c.json.gz --fmin=2 --every=4 --out=$R/stuck_${c}_f2e4.jsonl.gz > $R/stuck_${c}_f2e4.log
done
for c in hunt_n4_3_s400k hunt_n4_pure_s400k; do
  python3 k4/dl13_stuck.py catalog $G/$c.json.gz --fmin=2 --out=$R/stuck_${c}_f2.jsonl.gz > $R/stuck_${c}_f2.log
done
for c in hunt_n5_3_s2000 hunt_n5_4_s2000 hunt_n5_pure_s2000; do
  python3 k4/dl13_stuck.py catalog $G/$c.json.gz --every=2 --out=$R/stuck_${c}_e2.jsonl.gz > $R/stuck_${c}_e2.log
done
