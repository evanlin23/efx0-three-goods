#!/bin/bash
# n = 4 with identical agents (kgen/rounds.md §6): TWINS=1=3 (three types), TWINS=0=1,2=3 (two types); ROUND+ climbs
cd "$(dirname "$0")/../.." ; R=results/kgen_rounds; S=kgen/rounds/stress.py; export FAILS=$R/fails_twins.jsonl
for m in 7 8 9 10; do
  for k in generic pw bigsmall near; do
    TWINS=1=3 python3 $S climb 4 $m 4000 10 tw3n4m$m$k $k ties > $R/twins3_n4m${m}_${k}.log 2>&1
    TWINS=0=1,2=3 python3 $S climb 4 $m 3000 6 tw2n4m$m$k $k ties > $R/twins2_n4m${m}_${k}.log 2>&1
  done
done
TWINS=1=3 python3 $S climb 4 7 5000 20 tw3c4g named=GM4-G-lift ties > $R/twins3_n4m7_gm4g.log 2>&1
TWINS=1=2 python3 $S climb 4 7 5000 20 tw3rd5 named=RD5-lift ties > $R/twins3_n4m7_rd5_12.log 2>&1
