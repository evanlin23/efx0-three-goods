#!/bin/sh
# Referee runs for Lemma SD-E(round) (k4/oc1max_multi.md §17 at 85981d13).
cd "$(dirname "$0")"
python3 sder_ref.py 300000 1 &
python3 sder_ref.py 300000 2 &
python3 sder_ref.py 100000 3 anychain &
wait
