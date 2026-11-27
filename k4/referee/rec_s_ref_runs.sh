#!/bin/sh
# Referee runs for Lemma SD-E and Theorem REC-S (k4/oc1max_multi.md §12 at 6c3fd95). DATA: oc1max_cex12.jsonl and
# oc1_fail_walk.jsonl.gz from results/k4_oc1max_multi/ on proof/k4-oc1max-multi (read as data only).
cd "$(dirname "$0")"
C=${1:-../../results/k4_oc1max_multi/oc1max_cex12.jsonl}
W=${2:-../../results/k4_oc1max_multi/oc1_fail_walk.jsonl.gz}
python3 rec_s_ref.py data - "$C"
python3 rec_s_ref.py data - "$W"
python3 rec_s_ref.py data noK "$C" "$W"
python3 rec_s_ref.py data anychain "$C" "$W"
python3 rec_s_ref.py sde 30000 1
python3 rec_s_ref.py sde 10000 2 anychain
python3 rec_s_ref.py sde 10000 3 ties
python3 rec_s_ref.py recs 300000 4
python3 rec_s_ref.py recs 100000 5 noK
python3 rec_s_ref.py recs 100000 6 anychain
