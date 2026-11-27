#!/bin/sh
# Referee runs for the splice sketch (kgen/rounds.md §4.10 at f91c6bc8).
cd "$(dirname "$0")"
EXPORT=${1:-../../results/k4_oc1max/two_move_starts_n4.json.gz}
python3 splice_ref.py export "$EXPORT" 0 4
python3 splice_ref.py rand 100000 1 4
python3 splice_ref.py rand 300000 2 4
