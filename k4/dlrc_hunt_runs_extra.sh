#!/bin/sh
# compute/k4-rc, task (d), the remaining budget (after k4/dlrc_hunt_runs_final.sh): larger random samples of the n = 5
# cores with >= 3 four-good agents, big-top bias 0.5 (the failing profile of FAILURES.md has two big-top agents only),
# and the w2 / big-top climbs from the failing profiles. Resumable.
set -e
cd "$(dirname "$0")/.."
J=${JOBS:-$(nproc)}
H="python3 k4/dlrc_hunt.py"
F10=results/k4_rc/rt4_fail10_inst.json
$H certs_pure_x certs results/k4_certs_5_pure.json.gz --min4=3 --sample=1500 --steps=400 --bt=0.5 --jobs=$J --seed=61 >> results/k4_rc/hunt_certs_pure_x.log 2>&1
$H certs_n4_4_x certs results/k4_certs_5_n4_4.json.gz --min4=3 --sample=1500 --steps=400 --bt=0.5 --jobs=$J --seed=62 >> results/k4_rc/hunt_certs_n4_4_x.log 2>&1
$H certs_n4_3_x certs results/k4_certs_5_n4_3.json.gz --min4=3 --sample=1000 --steps=400 --bt=0.5 --jobs=$J --seed=63 >> results/k4_rc/hunt_certs_n4_3_x.log 2>&1
$H fail10_w2bt fail10 $F10 --reps=2 --steps=2000 --obj=w2 --bt=0.95 --jobs=$J --seed=22 >> results/k4_rc/hunt_fail10_w2bt.log 2>&1
