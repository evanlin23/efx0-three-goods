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
        run dumps dumps results/k4_rt4/dump_*.jsonl.gz results/k4_dl13*/*.jsonl.gz results/k4_dl2*/*.jsonl.gz --chunk=500 --jobs=${J:-4} --maxpairs=1000000 ;;
r3)     run r3 certs results/k4_certs_3.json.gz --sample=20 --seed=101 --jobs=${J:-4} ;;
r4)     run r4 certs results/k4_certs_4_n4_1.json.gz results/k4_certs_4_n4_2.json.gz results/k4_certs_4_n4_3.json.gz \
            results/k4_certs_4_pure.json.gz --sample=20 --seed=101 --jobs=${J:-4} ;;
r3b)    run r3b certs results/k4_certs_3.json.gz --sample=2000 --seed=102 --jobs=${J:-4} ;;
r4b)    run r4b certs results/k4_certs_4_n4_1.json.gz results/k4_certs_4_n4_2.json.gz results/k4_certs_4_n4_3.json.gz \
            results/k4_certs_4_pure.json.gz --sample=1000 --seed=102 --jobs=${J:-4} ;;
n5_4)   run n5_4 certs results/k4_certs_5_n4_4.json.gz --sample=4000 --seed=3 --jobs=${J:-4} --maxst=600 ;;
n5_purebt) run n5_purebt certs results/k4_certs_5_pure.json.gz --sample=5000 --seed=5 --bt=all --jobs=${J:-4} --maxst=600 ;;
n5_3)   run n5_3 certs results/k4_certs_5_n4_3.json.gz --sample=2000 --seed=3 --jobs=${J:-4} --maxst=600 ;;
n5_pure) run n5_pure certs results/k4_certs_5_pure.json.gz --sample=600 --seed=6 --jobs=${J:-4} --maxst=600 ;;
n5_12)  run n5_12 certs results/k4_certs_5_n4_1.json.gz results/k4_certs_5_n4_2.json.gz --sample=500 --seed=3 --jobs=${J:-4} --maxst=600 ;;
n6_1)   run n6_1 certs results/k4_certs_6_n4_1.json.gz --sample=100 --seed=3 --jobs=${J:-4} --maxst=600 ;;
x4_1)   run x4_1 certs results/k4_certs_4_n4_1.json.gz --sample=0 --jobs=${J:-4} --maxst=600 ;;   # every strict profile
x4_2)   run x4_2 certs results/k4_certs_4_n4_2.json.gz --sample=0 --jobs=${J:-4} --maxst=600 ;;   # every strict profile
n6_ext) run n6_ext certs results/k4_portfolio/cores_6_ext.json.gz --sample=5000 --seed=1 --jobs=${J:-4} --maxst=600 ;;  # k4/portfolio_ext6.py
big)    # 6 of the 11 dump profiles skipped by --maxpairs (H_2, n = 9, m = 23; at most 7.8M (state, P) pairs each; the other 5 have 30M-82M)
        run big inst results/k4_portfolio/big_profiles.json --chunk=1 --jobs=${J:-4} ;;
phase2) for r in dumps r3 r4 r3b r4b n5_4 n5_purebt n5_3 n5_12 n5_pure n6_1; do J=${J:-4} sh "$0" $r; done ;;
*)      echo "unknown run $1"; exit 2 ;;
esac
