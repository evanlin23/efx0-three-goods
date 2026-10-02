#!/bin/sh
# compute/k4-rc, task (b): k4/dlrc_ref.py (independent Python check on dl134_xcheck.py / c4x_check.py) against k4/dlrc.c.
set -e
cd "$(dirname "$0")/.."
J=${JOBS:-$(nproc)}
python3 k4/dlrc_ref.py inst results/k4_rc/rt4_fail10_inst.json --jobs=$J --expect-rt4fail=67 --expect-rcfail=0 > results/k4_rc/ref_fail10.log 2>&1
python3 k4/dlrc_ref.py tsv results/k4_dl13/n4_failures_n4_1.tsv results/k4_dl13/n4_failures_n4_2.tsv \
  results/k4_dl13/n4_failures_n4_3_s200b.tsv --jobs=$J > results/k4_rc/ref_n4_failures.log 2>&1
python3 k4/dlrc_ref.py suite --jobs=$J > results/k4_rc/ref_suite.log 2>&1
python3 k4/dlrc_ref.py random results/k4_certs_3.json.gz --want=800 --neg=200 --seed=1 --jobs=$J > results/k4_rc/ref_random_n3.log 2>&1
python3 k4/dlrc_ref.py random results/k4_certs_4_n4_1.json.gz results/k4_certs_4_n4_2.json.gz results/k4_certs_4_n4_3.json.gz \
  results/k4_certs_4_pure.json.gz --want=800 --neg=200 --seed=1 --jobs=$J > results/k4_rc/ref_random_n4.log 2>&1
