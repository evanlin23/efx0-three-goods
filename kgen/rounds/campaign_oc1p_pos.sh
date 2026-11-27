#!/bin/bash
# OC1' at strictly positive values (kgen/rounds.md §4.6): zclimb.py ZFREE=1 ZCLASS=OC1P, random and seeded from the
# ROUND+ failures (where OC1 and one round fail)
cd "$(dirname "$0")/../.." ; R=results/kgen_rounds; Z=kgen/rounds/zclimb.py; export FAILS=$R/fails_oc1p_pos.jsonl ZCLASS=OC1P ZFREE=1
python3 $Z 4 7 4000 20 pp4s seeds=$R/seeds3_n4m7.jsonl > $R/oc1p_pos_n4m7_seeded.log 2>&1
python3 $Z 5 9 2000 8 pp5s seeds=$R/seeds3_n5m9.jsonl > $R/oc1p_pos_n5m9_seeded.log 2>&1
for m in 7 8 9; do python3 $Z 4 $m 4000 15 pp4$m > $R/oc1p_pos_n4m${m}.log 2>&1; done
for m in 8 9; do python3 $Z 5 $m 2000 6 pp5$m > $R/oc1p_pos_n5m${m}.log 2>&1; done
