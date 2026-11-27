#!/bin/bash
# eps-lifted k = 4 instances with no worthless good (KEPS=4 KCOVER=1), ROUND+ climbs (kgen/rounds.md §4.3)
cd "$(dirname "$0")/../.." ; R=results/kgen_rounds; S=kgen/rounds/stress.py; export FAILS=$R/fails_kcover.jsonl KEPS=4 KCOVER=1
for m in 6 7 8 9; do for f in generic pw bigsmall corr near; do python3 $S climb 4 $m 4000 10 kc4n4m$m$f $f ties > $R/kcover4_n4m${m}_${f}.log 2>&1; done; done
for m in 7 8 9 10; do for f in generic pw bigsmall; do python3 $S climb 5 $m 3000 6 kc4n5m$m$f $f ties > $R/kcover4_n5m${m}_${f}.log 2>&1; done; done
