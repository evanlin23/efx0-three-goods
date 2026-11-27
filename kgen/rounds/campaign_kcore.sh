#!/bin/bash
# eps-lifted k = 4 CORES (KEPS=4 KCORE=1: the zero version satisfies k4/SCOUT.md K4.CORE), ROUND+ climbs; every
# eps-failure's zero version is then checked against OC1^max with three programs (k4zero_scan.py)
cd "$(dirname "$0")/../.." ; R=results/kgen_rounds; S=kgen/rounds/stress.py; export FAILS=$R/fails_kcore.jsonl KEPS=4 KCORE=1
for rep in 1 2; do
for m in 6 7 8 9; do for f in generic pw bigsmall corr near; do python3 $S climb 4 $m 4000 10 kco$rep${m}$f $f ties > $R/kcore4_n4m${m}_${f}_$rep.log 2>&1; done; done
for m in 7 8 9 10; do for f in generic pw bigsmall; do python3 $S climb 5 $m 3000 6 kco5$rep$m$f $f ties > $R/kcore4_n5m${m}_${f}_$rep.log 2>&1; done; done
done
