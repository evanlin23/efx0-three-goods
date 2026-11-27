#!/bin/bash
# campaign 4 (kgen/rounds.md §4.1): climbs toward three rounds with rnd.c's exact two-round count (climb3.py)
cd "$(dirname "$0")/../.." ; R=results/kgen_rounds; C=kgen/rounds/climb3.py; export FAILS3=$R/fails3.jsonl
lane1() { for s in n4m7 n4m8 n4m9; do python3 $C 4 7 3000 25 c4$s seeds=$R/seeds3_$s.jsonl 3 > $R/c4_3r_$s.log 2>&1; done; for m in 7 8 9 10; do for k in generic pw bigsmall near; do python3 $C 4 $m 3000 10 c4n4m$m$k $k 3 > $R/c4_3r_n4m${m}_${k}.log 2>&1; done; done; }
lane2() { for s in n5m8 n5m9; do python3 $C 5 8 1500 12 c4$s seeds=$R/seeds3_$s.jsonl 2 > $R/c4_3r_$s.log 2>&1; done; for m in 8 9; do for k in generic pw; do python3 $C 5 $m 1500 6 c4n5m$m$k $k 2 > $R/c4_3r_n5m${m}_${k}.log 2>&1; done; done; }
lane1 & lane2 & wait
