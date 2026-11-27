#!/bin/bash
# OC1'^max stress, round 2 (kgen/rounds.md §4.6): seeded from every OC1^max counterexample, and random n = 5 cores
cd "$(dirname "$0")/../.." ; R=results/kgen_rounds; Z=kgen/rounds/zclimb.py; export FAILS=$R/fails_oc1p.jsonl ZCLASS=OC1P
lane1() { for rep in 1 2 3 4; do python3 $Z 4 7 5000 25 q4s$rep seeds=$R/fails_zcore.jsonl > $R/oc1pB_n4m7_zseeded_$rep.log 2>&1; done; }
lane2() { for rep in 1 2; do for m in 8 9 10; do python3 $Z 5 $m 3000 10 q5$m$rep > $R/oc1pB_n5m${m}_$rep.log 2>&1; done; done; }
lane3() { for rep in 1 2; do for m in 6 7 8; do python3 $Z 4 $m 5000 30 q4$m$rep > $R/oc1pB_n4m${m}_$rep.log 2>&1; done; done; }
lane1 & lane2 & lane3 & wait
