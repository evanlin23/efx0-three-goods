#!/bin/bash
# eps-lifted instances of the shape of Lemma RED's I' (k4/sdc.md §31): agents of KEPS3 have 3 real goods and may be
# top-heavy, the others 4 and strictly balanced, every good real for someone (KEPS=4 KIPRIME=1); ROUND+ climbs; every
# eps-failure's zero version is checked with three programs (k4zero_scan.py)
cd "$(dirname "$0")/../.." ; R=results/kgen_rounds; S=kgen/rounds/stress.py; export FAILS=$R/fails_iprime.jsonl KEPS=4 KIPRIME=1
for e3 in 2 0,2 1,2; do for m in 6 7 8; do for f in generic pw bigsmall corr; do
  KEPS3=$e3 python3 $S climb 4 $m 4000 8 ip$e3$m$f $f ties > $R/iprime_n4m${m}_${f}_e${e3/,/_}.log 2>&1
done; done; done
for e3 in 2 1,3; do for m in 7 8 9; do for f in generic pw; do
  KEPS3=$e3 python3 $S climb 5 $m 3000 5 ip5$e3$m$f $f ties > $R/iprime_n5m${m}_${f}_e${e3/,/_}.log 2>&1
done; done; done
