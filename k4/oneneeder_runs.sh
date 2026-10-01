#!/bin/sh
# The runs of k4/oneneeder.md section 6 (one process at a time). Logs and dumps in results/k4_oneneeder/.
set -e
R=results/k4_oneneeder
python3 k4/oneneeder_run.py certs results/k4_certs_3.json.gz --dump=$R/certs3_all.jsonl.gz --rep=2000 --ckpt=$R/certs3_all.ckpt > $R/certs3_all.log 2>&1
python3 k4/oneneeder_run.py certs results/k4_certs_3.json.gz --sample=20000 --seed=11 --dump=$R/certs3_r20000_s11.jsonl.gz --rep=200 > $R/certs3_r20000_s11.log 2>&1
for c in gap_n4_1 gap_n4_2_s4000 gap_n4_3_s4000 gap_n4_pure_s4000 gap_n5_1_s100 gap_n5_2_s100 gap_n5_3_s100 gap_n5_4_s100 gap_n5_pure_s100 hard_hunt hunt_n4_2_all hunt_n4_3_s400k hunt_n4_pure_s400k hunt_n5_3_s2000 hunt_n5_4_s2000 hunt_n5_pure_s2000; do
  python3 k4/oneneeder_run.py catalog results/k4_gap/$c.json.gz --dump=$R/cat_$c.jsonl.gz --rep=20 > $R/cat_$c.log 2>&1
done
