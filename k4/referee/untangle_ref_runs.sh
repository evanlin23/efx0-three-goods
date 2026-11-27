#!/bin/sh
# Referee runs for Lemma UNTANGLE (kgen/rounds.md §4.13 at 50c1fc44); log results/k4_referee/untangle_ref.log
cd "$(dirname "$0")"
python3 untangle_ref.py 800 1 4 7 4
python3 untangle_ref.py 150 2 5 7 4
