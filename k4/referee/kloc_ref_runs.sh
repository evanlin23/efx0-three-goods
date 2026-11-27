#!/bin/sh
# Referee runs for Lemma WG and Proposition K-loc (k4/oc1max_multi.md §13-§14 at 6b6cf7b); the phantom-class instance.
cd "$(dirname "$0")"
EXPORT=${1:-../../results/k4_oc1max/two_move_starts_n4.json.gz}
WALK=${2:-../../results/k4_oc1max_multi/oc1_fail_walk.jsonl.gz}
python3 kloc_ref.py export "$EXPORT" 4
python3 kloc_ref.py jsonl "$WALK" 4
python3 kloc_ref.py wg 20000 1
python3 phantom_ref.py export "$EXPORT" 4
python3 phantom_ref.py jsonl "$WALK" 4
python3 phantom_cex.py
