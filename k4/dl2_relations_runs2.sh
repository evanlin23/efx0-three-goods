#!/bin/sh
# DL_R on whole certificate files, f = 0 profiles included (k4/dl2.md §3): every strict profile of every n = 2 core,
# seeded random profiles per core for n = 3 and n = 4. Two worker processes (J=1 for one). Output: results/k4_dl2_relations/.
set -e
cd "$(dirname "$0")/.."
R=results/k4_dl2_relations
python3 k4/dl2_relations.py certs results/k4_certs_2.json.gz --jobs=${J:-2} --out=$R/certs_2_all.jsonl.gz > $R/certs_2_all.log 2>&1
python3 k4/dl2_relations.py certs results/k4_certs_3.json.gz --rand=400 --seed=3 --jobs=${J:-2} --out=$R/certs_3_r400.jsonl.gz > $R/certs_3_r400.log 2>&1
for c in 4_n4_1 4_n4_2 4_n4_3 4_pure; do
  python3 k4/dl2_relations.py certs results/k4_certs_$c.json.gz --rand=20 --seed=4 --jobs=${J:-2} --out=$R/certs_${c}_r20.jsonl.gz > $R/certs_${c}_r20.log 2>&1
done
