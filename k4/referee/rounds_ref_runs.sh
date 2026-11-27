#!/bin/sh
# Referee runs for k4/referee/rounds_r1.md (log: results/k4_referee/rounds_ref.log)
cd "$(dirname "$0")"
python3 rounds_ref.py named
python3 rounds_ref.py 3000 3 4 1
