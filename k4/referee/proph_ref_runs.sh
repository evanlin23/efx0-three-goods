#!/bin/sh
# Referee runs for k4/referee/proph.md (log: results/k4_referee/proph_ref.log)
cd "$(dirname "$0")"
python3 proph_ref.py 3000 1          # delta = 1 < Q = 100: the restriction must be exactly EFX0
python3 proph_ref.py 1000 2 350      # delta = 350 > Q: shows the delta -> 0 step is needed
