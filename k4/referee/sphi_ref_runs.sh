#!/bin/sh
# Referee runs for Theorem S^phi (k4/oc1max_multi.md §16 at 52f5b0b6).
cd "$(dirname "$0")"
EXPORT=${1:-../../results/k4_oc1max/two_move_starts_n4.json.gz}
WALK=${2:-../../results/k4_oc1max_multi/oc1_fail_walk.jsonl.gz}
python3 sphi_ref.py export "$EXPORT" 4
python3 sphi_ref.py jsonl "$WALK" 4
python3 sphi_ref.py rand 1500000:2 4
