#!/bin/bash
# OC1'^max stress (kgen/rounds.md §4.6): direct zero-value k = 4 core climbs with ZCLASS=OC1P, seeded from the OC1
# failures and random cores
cd "$(dirname "$0")/../.." ; R=results/kgen_rounds; Z=kgen/rounds/zclimb.py; export FAILS=$R/fails_oc1p.jsonl ZCLASS=OC1P
for rep in 1 2 3; do
  python3 $Z 4 7 4000 20 p4s$rep seeds=$R/fails_kcore.jsonl > $R/oc1p_n4m7_seeded_$rep.log 2>&1
  for m in 6 7 8; do python3 $Z 4 $m 4000 30 p4$m$rep > $R/oc1p_n4m${m}_$rep.log 2>&1; done
  for m in 7 8 9; do python3 $Z 5 $m 3000 10 p5$m$rep > $R/oc1p_n5m${m}_$rep.log 2>&1; done
done
