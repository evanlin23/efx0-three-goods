#!/bin/sh
# DL13 at f >= 2 with the frozen rotations of Lemma 12 (k4/dl13.md §2.2): every def > 0 state records whether it is
# T4-optimal and its improving (T4) moves, and Lemma 12 is asserted at every state. Inputs: compute/k4-dl13's DL13
# failures at n = 4 (results/k4_dl13/n4_failures_*.tsv, on main since #74 and identical to those of 0617abf, which
# made the logs; copy them to k4/suite/.cache/compute_k4_dl13/), and the inputs of k4/dl13_stuck_runs.sh with f >= 2.
# One worker, sequential; about an hour. Needs #53's catalogues in k4/suite/.cache/gapbench (k4/strategy.md §4).
set -e
G=k4/suite/.cache/gapbench/results/k4_gap
C=k4/suite/.cache/compute_k4_dl13
R=results/k4_dl13_stuck
mkdir -p $R
for f in n4_1 n4_2 n4_3_s200b; do
  python3 k4/dl13_stuck.py tsv $C/n4_failures_$f.tsv --out=$R/t4_failures_$f.jsonl.gz | grep -v '^DL13-FAILS' > $R/t4_failures_$f.log
done
python3 k4/dl13_stuck.py suite --out=$R/t4_suite.jsonl.gz > $R/t4_suite.log
python3 k4/dl13_stuck.py catalog $G/hard_hunt.json.gz --out=$R/t4_hard_hunt.jsonl.gz > $R/t4_hard_hunt.log
for c in gap_n4_1 gap_n4_2_s4000 gap_n4_3_s4000 gap_n4_pure_s4000 hunt_n4_3_s400k hunt_n4_pure_s400k; do
  python3 k4/dl13_stuck.py catalog $G/$c.json.gz --fmin=2 --out=$R/t4_${c}_f2.jsonl.gz > $R/t4_${c}_f2.log
done
for c in gap_n5_1_s100 gap_n5_2_s100 gap_n5_3_s100 gap_n5_4_s100 gap_n5_pure_s100; do
  python3 k4/dl13_stuck.py catalog $G/$c.json.gz --fmin=2 --every=4 --out=$R/t4_${c}_f2e4.jsonl.gz > $R/t4_${c}_f2e4.log
done
python3 k4/dl13_stuck.py certs results/k4_certs_3.json.gz --rand=2000 --seed=13 --out=$R/t4_certs_3_r2000.jsonl.gz > $R/t4_certs_3_r2000.log
for c in 4_n4_1 4_n4_2 4_n4_3 4_pure; do
  python3 k4/dl13_stuck.py certs results/k4_certs_$c.json.gz --rand=100 --seed=13 --out=$R/t4_certs_${c}_r100.jsonl.gz > $R/t4_certs_${c}_r100.log
done
