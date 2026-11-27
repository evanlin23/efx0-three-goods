#!/bin/bash
# core-constrained eps-lift climbs, round 2 (kgen/rounds.md §4.4): more k = 4 core counterexamples to OC1^max
cd "$(dirname "$0")/../.." ; R=results/kgen_rounds; S=kgen/rounds/stress.py; export FAILS=$R/fails_kcore.jsonl KEPS=4 KCORE=1
lane() { for rep in $1; do for m in 6 7 8; do for f in generic pw bigsmall corr near small tops; do python3 $S climb 4 $m 4000 12 kcB$rep$m$f $f ties > $R/kcoreB_n4m${m}_${f}_$rep.log 2>&1; done; done; done; }
lane5() { for rep in $1; do for m in 7 8 9; do for f in generic pw bigsmall corr; do python3 $S climb 5 $m 3000 6 kcB5$rep$m$f $f ties > $R/kcoreB_n5m${m}_${f}_$rep.log 2>&1; done; done; done; }
lane "1 3" & lane "2 4" & lane5 "1 2" & wait
