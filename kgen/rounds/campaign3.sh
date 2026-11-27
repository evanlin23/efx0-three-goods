#!/bin/bash
# campaign 3 (kgen/rounds.md §2, §4): larger climbs.  Lanes 1-2: ROUND+ (CLASS=RND1) at n = 4, m = 8..12 and n = 5;
# lane 3: ROUND-X (CLASS=RNDX1) from the one-round failures' seeds (RD5-lift, GM4) and random at n = 4, 5.
cd "$(dirname "$0")/../.." ; R=results/kgen_rounds; S=kgen/rounds/stress.py; export FAILS=$R/fails.jsonl
lane1() { for m in 8 9 10 11 12; do for k in generic pw bigsmall corr near; do CLASS=RND1 python3 $S climb 4 $m 4000 12 c3n4m$m$k $k ties > $R/c3_rnd1_n4m${m}_${k}.log 2>&1; done; done; }
lane2() { for m in 8 9 10; do for k in generic pw bigsmall corr; do CLASS=RND1 python3 $S climb 5 $m 4000 6 c3n5m$m$k $k ties > $R/c3_rnd1_n5m${m}_${k}.log 2>&1; done; done; }
lane3() { for g in RD5-lift GM4-A-lift GM4-G-lift GM4-E-lift kgenN4-lift; do CLASS=RNDX1 python3 $S climb 4 7 5000 15 c3x$g named=$g ties > $R/c3_rndx_n4_$g.log 2>&1; done; CLASS=RNDX1 python3 $S climb 5 9 4000 8 c3xpw5 named=PW5-lift ties > $R/c3_rndx_n5m9_pw5.log 2>&1; for m in 7 8 9 10; do for k in generic pw bigsmall; do CLASS=RNDX1 python3 $S climb 4 $m 4000 10 c3xn4m$m$k $k ties > $R/c3_rndx_n4m${m}_${k}.log 2>&1; done; done; }
lane1 & lane2 & lane3 & wait
