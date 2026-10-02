#!/bin/sh
# NOT RUN: superseded for the time budget by k4/dlrc_hunt_runs_final.sh (which runs fail10_w2 with --reps=2).
# compute/k4-rc, task (d), third batch (sizes cut for the time budget) (after k4/dlrc_hunt_runs2.sh): objective k3 (distance terms before the gap) with a
# strong big-top bias (--bt=0.95), on the top-ranked and random n = 5 cores with >= 3 four-good agents. Resumable.
set -e
cd "$(dirname "$0")/.."
J=${JOBS:-$(nproc)}
T=${TMPDIR:-/tmp}/k4_rc_ckpts; mkdir -p $T
for b in n5b:ckpt_n5b_3 n5b:ckpt_n5b_3bt n5b:ckpt_n5b_4 n5c:ckpt_n5c_pure n5c:ckpt_n5c_purebt; do
  [ -s $T/${b#*:}.jsonl ] || git show origin/compute/k4-rt4-${b%%:*}:results/k4_rt4/${b#*:}.jsonl > $T/${b#*:}.jsonl
done
H="python3 k4/dlrc_hunt.py"
$H ranked_pure_k3 ranked results/k4_certs_5_pure.json.gz $T/ckpt_n5c_pure.jsonl $T/ckpt_n5c_purebt.jsonl results/k4_rc/ckpt_c_purebt.jsonl --top=60 --steps=1000 --obj=k3 --bt=0.95 --jobs=$J --seed=31 >> results/k4_rc/hunt_ranked_pure_k3.log 2>&1
$H ranked_n4_4_k3 ranked results/k4_certs_5_n4_4.json.gz $T/ckpt_n5b_4.jsonl results/k4_rc/ckpt_c_n4_4.jsonl --top=60 --steps=1000 --obj=k3 --bt=0.95 --jobs=$J --seed=32 >> results/k4_rc/hunt_ranked_n4_4_k3.log 2>&1
$H certs_pure_k3 certs results/k4_certs_5_pure.json.gz --min4=3 --sample=300 --steps=400 --obj=k3 --bt=0.95 --jobs=$J --seed=34 >> results/k4_rc/hunt_certs_pure_k3.log 2>&1
# (cut for the time budget: ranked n4_3 and random n4_3 / n4_4 samples with k3)
