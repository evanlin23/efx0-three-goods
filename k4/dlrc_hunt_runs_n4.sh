#!/bin/sh
# compute/k4-rc, after the DL_RC failure at n = 5 (results/k4_rc/FAILURES.md): hunt every n = 4 core with three or four
# four-good agents (the earlier dlrt4.c runs enumerated the n = 4 cores with one or two exhaustively, sampled these).
set -e
cd "$(dirname "$0")/.."
J=${JOBS:-$(nproc)}
H="python3 k4/dlrc_hunt.py"
$H n4_pure certs results/k4_certs_4_pure.json.gz --steps=600 --jobs=$J --seed=41 >> results/k4_rc/hunt_n4_pure.log 2>&1
$H n4_n4_3 certs results/k4_certs_4_n4_3.json.gz --steps=600 --jobs=$J --seed=42 >> results/k4_rc/hunt_n4_n4_3.log 2>&1
$H n4_pure_k3 certs results/k4_certs_4_pure.json.gz --steps=600 --obj=k3 --bt=0.9 --jobs=$J --seed=43 >> results/k4_rc/hunt_n4_pure_k3.log 2>&1
$H n4_n4_3_k3 certs results/k4_certs_4_n4_3.json.gz --steps=600 --obj=k3 --bt=0.9 --jobs=$J --seed=44 >> results/k4_rc/hunt_n4_n4_3_k3.log 2>&1
