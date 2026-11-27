#!/bin/sh
# The censuses of k4/oc1max_multi.md on the committed starts (run from the repository root after runs.sh).
R=results/k4_oc1max_multi; D="$R/hard2_starts.jsonl.gz $R/hard2_starts_n5.jsonl.gz"
python3 k4/oc1max_multi/analyze.py $D > $R/analyze.log
python3 k4/oc1max_multi/dred.py $D > $R/dred.log
python3 k4/oc1max_multi/theta.py $D > $R/theta.log
python3 k4/oc1max_multi/lemma_b.py $D > $R/lemma_keep.log
sh k4/oc1max_multi/analyses2.sh
