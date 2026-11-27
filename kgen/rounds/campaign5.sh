#!/bin/bash
# campaign 5 (kgen/rounds.md §4.1): three-round climbs with the two-round MARGIN (climb3.py, MARGIN2=1)
cd "$(dirname "$0")/../.." ; R=results/kgen_rounds; C=kgen/rounds/climb3.py; export FAILS3=$R/fails3.jsonl MARGIN2=1 PHASED=1
lane1() { for s in n4m7 n4m8 n4m9; do python3 $C 4 7 2500 20 c5$s seeds=$R/seeds3_$s.jsonl 3 > $R/c5_3r_$s.log 2>&1; done; for m in 7 8; do for k in generic pw bigsmall; do python3 $C 4 $m 2500 8 c5n4m$m$k $k 3 > $R/c5_3r_n4m${m}_${k}.log 2>&1; done; done; }
lane2() { python3 $C 4 7 2500 20 c5kc seeds=$R/fails_kcover.jsonl 3 > $R/c5_3r_kcover.log 2>&1; python3 $C 4 7 2500 20 c5ke seeds=$R/fails_keps.jsonl 3 > $R/c5_3r_keps.log 2>&1; python3 $C 4 7 2500 20 c5tw seeds=$R/fails_twins.jsonl 3 > $R/c5_3r_twins.log 2>&1; }
lane1 & lane2 & wait
