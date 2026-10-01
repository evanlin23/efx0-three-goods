#!/bin/sh
# The Phase 2 runs of compute/k4-portfolio (k4/portfolio.py). Each is resumable (--ckpt): rerun the same line after a kill.
# Logs and aggregates in results/k4_portfolio/.
set -e
cd "$(dirname "$0")/.."
R=results/k4_portfolio
run() { name=$1; shift; python3 k4/portfolio.py "$@" --name=$name --ckpt >> $R/$name.log 2>&1; }
case "$1" in
suite)  python3 k4/portfolio.py suite --name=suite --jobs=3 --chunk=5 > $R/suite.log 2>&1 ;;
dumps)  # every distinct profile of the D records (dlrt4.c, dl13.c, dl2.c dumps) under results/k4_rt4, k4_dl13*, k4_dl2*
        run dumps dumps results/k4_rt4/dump_*.jsonl.gz results/k4_dl13*/*.jsonl.gz results/k4_dl2*/*.jsonl.gz --chunk=500 --jobs=${J:-4} ;;
r3)     run r3 certs results/k4_certs_3.json.gz --sample=20 --seed=101 --jobs=${J:-4} ;;
r4)     run r4 certs results/k4_certs_4_n4_1.json.gz results/k4_certs_4_n4_2.json.gz results/k4_certs_4_n4_3.json.gz \
            results/k4_certs_4_pure.json.gz --sample=20 --seed=101 --jobs=${J:-4} ;;
*)      echo "unknown run $1"; exit 2 ;;
esac
