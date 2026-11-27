#!/bin/bash
# eps-lifted k-limited instances (kgen/rounds.md §4.3): KEPS=4 and KEPS=5, ROUND+ climbs at n = 4, 5
cd "$(dirname "$0")/../.." ; R=results/kgen_rounds; S=kgen/rounds/stress.py; export FAILS=$R/fails_keps.jsonl
for k in 4 5; do
  KEPS=$k python3 $S climb 4 7 4000 10 ke${k}rd5 named=RD5-lift ties > $R/keps${k}_n4m7_rd5.log 2>&1
  for m in 7 8 9; do for f in generic pw bigsmall; do KEPS=$k python3 $S climb 4 $m 4000 8 ke${k}n4m$m$f $f ties > $R/keps${k}_n4m${m}_${f}.log 2>&1; done; done
  for m in 8 9; do for f in generic pw; do KEPS=$k python3 $S climb 5 $m 3000 5 ke${k}n5m$m$f $f ties > $R/keps${k}_n5m${m}_${f}.log 2>&1; done; done
  KEPS=$k python3 $S climb 5 9 3000 8 ke${k}pw5 named=PW5-lift ties > $R/keps${k}_n5m9_pw5.log 2>&1
done
