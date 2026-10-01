#!/bin/sh
# T1-stuck states of DL13 (k4/dl13.md §1): the suite, #53's catalogues and hunts, random profiles of the certified
# core lists. One worker, sequential; about two hours.
# Needs the catalogues at 245040b in k4/suite/.cache/gapbench (k4/strategy.md §4).
set -e
G=k4/suite/.cache/gapbench/results/k4_gap
R=results/k4_dl13_stuck
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
# seeded random profiles of the certified core lists (f = 0 profiles are skipped)
python3 k4/dl13_stuck.py certs results/k4_certs_3.json.gz --rand=2000 --seed=13 --out=$R/stuck_certs_3_r2000.jsonl.gz > $R/stuck_certs_3_r2000.log
for c in 4_n4_1 4_n4_2 4_n4_3 4_pure; do
  python3 k4/dl13_stuck.py certs results/k4_certs_$c.json.gz --rand=100 --seed=13 --out=$R/stuck_certs_${c}_r100.jsonl.gz > $R/stuck_certs_${c}_r100.log
done
for c in 5_n4_1 5_n4_2 5_n4_3 5_n4_4 5_pure; do
  python3 k4/dl13_stuck.py certs results/k4_certs_$c.json.gz --rand=4 --seed=13 --out=$R/stuck_certs_${c}_r4.jsonl.gz > $R/stuck_certs_${c}_r4.log
done
python3 k4/dl13_table.py $R/stuck_*.log > $R/table.md
