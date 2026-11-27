#!/bin/sh
# The second half of analyses.sh (run from the repository root).
R=results/k4_oc1max_multi; D="$R/hard2_starts.jsonl.gz $R/hard2_starts_n5.jsonl.gz"
python3 k4/oc1max_multi/regimes.py $D > $R/regimes.log
python3 k4/oc1max_multi/lemma_set.py $D > $R/lemma_set.log
python3 k4/oc1max_multi/lemma_own.py $D > $R/lemma_own.log
python3 k4/oc1max_multi/ring.py $D > $R/ring.log
python3 k4/oc1max_multi/slot_stats.py $D > $R/slot_stats.log
[ -n "$HALL" ] && HALL=$HALL python3 k4/oc1max_multi/xcheck_hall.py $R/hard2_starts.jsonl.gz > $R/xcheck_hall.log
python3 k4/oc1max_multi/theorem_u1.py $D > $R/theorem_u.log
python3 k4/oc1max_multi/ring_comp.py $D > $R/ring_comp.log
