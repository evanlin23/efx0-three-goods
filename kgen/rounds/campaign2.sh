#!/bin/bash
# ROUND+ climb campaign 2 (kgen/rounds.md §2): 4 lanes; every one-round failure is appended to results/kgen_rounds/fails.jsonl
cd "$(dirname "$0")/../.." ; R=results/kgen_rounds; S=kgen/rounds/stress.py; export FAILS=$R/fails.jsonl
lane1() { for g in A B C D E G; do python3 $S climb 4 7 3000 8 gm4$g named=GM4-$g-lift ties > $R/climb_n4m7_gm4${g}.log 2>&1; done; python3 $S climb 4 7 3000 10 rd5 named=RD5-lift ties > $R/climb_n4m7_rd5.log 2>&1; python3 $S climb 4 8 3000 10 kgn4 named=kgenN4-lift ties > $R/climb_n4m8_kgenN4.log 2>&1; }
lane2() { for m in 8 9 10; do for k in generic near tops pw; do python3 $S climb 4 $m 2500 6 n4m$m$k $k ties > $R/climb_n4m${m}_${k}.log 2>&1; done; done; }
lane3() { python3 $S climb 5 9 2000 6 pw5 named=PW5-lift ties > $R/climb_n5m9_pw5.log 2>&1; for m in 8 9 10; do for k in generic pw corr; do python3 $S climb 5 $m 1500 4 n5m$m$k $k ties > $R/climb_n5m${m}_${k}.log 2>&1; done; done; }
lane4() { for m in 6 7 8 9 10; do for k in generic near tops small; do python3 $S climb 3 $m 3000 8 n3m$m$k $k ties > $R/climb_n3m${m}_${k}.log 2>&1; done; done; python3 $S climb 3 7 3000 10 cgm named=CGM-barrier-lift ties > $R/climb_n3m7_cgm.log 2>&1; }
lane1 & lane2 & lane3 & lane4 & wait
