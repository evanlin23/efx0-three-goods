#!/bin/bash
# direct zero-value k = 4 core climbs toward OC1^max failures (zclimb.py, kgen/rounds.md §4.5)
cd "$(dirname "$0")/../.." ; R=results/kgen_rounds; Z=kgen/rounds/zclimb.py; export FAILS=$R/fails_zcore.jsonl
for rep in 1 2 3; do
  for m in 6 7 8; do python3 $Z 4 $m 4000 40 zc4$m$rep > $R/zcore_n4m${m}_$rep.log 2>&1; done
  python3 $Z 4 7 4000 20 zcs$rep seeds=$R/fails_kcore.jsonl > $R/zcore_n4m7_seeded_$rep.log 2>&1
  for m in 7 8 9; do python3 $Z 5 $m 3000 12 zc5$m$rep > $R/zcore_n5m${m}_$rep.log 2>&1; done
done
