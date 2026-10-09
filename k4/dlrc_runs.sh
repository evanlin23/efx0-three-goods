#!/bin/sh
# compute/k4-rc, task (c): DL_RC on the two inputs that produced the n = 5 DL_RT4 failures. Resumable: re-run this script
# (each run has its own checkpoint, dump and log under results/k4_rc/; a resumed run appends a second header to its log).
set -e
cd "$(dirname "$0")/.."
J=${JOBS:-$(nproc)}
# the n5c slice's big-top pure run (compute/k4-rt4-n5c: n5c_purebt)
python3 k4/dlrc_run.py certs results/k4_certs_5_pure.json.gz --sample=5000 --seed=2 --bt=all --jobs=$J --progress \
  --ckpt=results/k4_rc/ckpt_c_purebt.jsonl --dump=results/k4_rc/dump_c_purebt.jsonl.gz \
  --tables=results/k4_rc/tables_c_purebt.json >> results/k4_rc/c_purebt.log 2>&1
# the n5b run on k4_certs_5_n4_4 (compute/k4-rt4-n5b: n5b_4)
python3 k4/dlrc_run.py certs results/k4_certs_5_n4_4.json.gz --sample=16000 --seed=1 --jobs=$J --progress \
  --ckpt=results/k4_rc/ckpt_c_n4_4.jsonl --dump=results/k4_rc/dump_c_n4_4.jsonl.gz \
  --tables=results/k4_rc/tables_c_n4_4.json >> results/k4_rc/c_n4_4.log 2>&1
