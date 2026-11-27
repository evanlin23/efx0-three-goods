#!/bin/sh
# Referee runs for Theorem ROUND-SIMPLE (kgen/rounds.md §4.11 at d79599ea). $1: the certifier's n = 4 export.
cd "$(dirname "$0")"
python3 roundsimple_ref.py rand 600 1 4
python3 roundsimple_ref.py export "$1" 400 4
