#!/bin/bash
# ROUND+ climb campaign 1 (kgen/rounds.md §2): 4 parallel lanes.  Logs in results/kgen_rounds/.
cd "$(dirname "$0")/../.." ; R=results/kgen_rounds; S=kgen/rounds/stress.py
lane1() { for g in A B C D E G; do python3 $S climb 4 7 3000 8 1$g named=GM4-$g-lift ties > $R/climb_n4m7_gm4${g}.log 2>&1; done; python3 $S climb 4 7 3000 10 17 named=RD5-lift ties > $R/climb_n4m7_rd5.log 2>&1; }
lane2() { for m in 8 9 10; do for k in generic near tops pw; do python3 $S climb 4 $m 2500 6 2$m$k $k ties > $R/climb_n4m${m}_${k}.log 2>&1; done; done; }
lane3() { python3 $S climb 5 9 2000 6 39 named=PW5-lift ties > $R/climb_n5m9_pw5.log 2>&1; for m in 8 9 10; do for k in generic pw corr; do python3 $S climb 5 $m 1500 4 3$m$k $k ties > $R/climb_n5m${m}_${k}.log 2>&1; done; done; }
lane4() { python3 $S rand all 4 10 12 12000 41 > $R/rand_n4_10_12_12000_41.log 2>&1; python3 $S climb 3 8 3000 10 48 generic ties > $R/climb_n3m8_generic.log 2>&1; python3 $S climb 3 9 3000 10 49 near ties > $R/climb_n3m9_near.log 2>&1; }
lane1 & lane2 & lane3 & lane4 & wait
