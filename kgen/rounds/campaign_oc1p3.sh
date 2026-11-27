#!/bin/bash
# OC1'^max and OC1^max at n = 6, 7 on k = 4 cores with zeros (kgen/rounds.md §4.6)
cd "$(dirname "$0")/../.." ; R=results/kgen_rounds; Z=kgen/rounds/zclimb.py
lane1() { for m in 9 10 11 12; do FAILS=$R/fails_oc1p.jsonl ZCLASS=OC1P python3 $Z 6 $m 3000 8 r6$m > $R/oc1pC_n6m${m}.log 2>&1; done; for m in 11 12; do FAILS=$R/fails_oc1p.jsonl ZCLASS=OC1P python3 $Z 7 $m 2000 5 r7$m > $R/oc1pC_n7m${m}.log 2>&1; done; }
lane2() { for m in 9 10 11 12; do FAILS=$R/fails_zcore.jsonl ZCLASS=OC1 python3 $Z 6 $m 3000 8 s6$m > $R/zcoreC_n6m${m}.log 2>&1; done; }
lane1 & lane2 & wait
