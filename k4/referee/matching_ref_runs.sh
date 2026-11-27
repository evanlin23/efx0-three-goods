#!/bin/sh
# Referee runs for k4/referee/matching.md (log: results/k4_referee/matching_ref.log)
cd "$(dirname "$0")"
python3 matching_ref.py cases
python3 matching_ref.py 6000 3 4 4 8 1
python3 matching_ref.py 6000 3 5 5 9 2
python3 matching_ref.py 3000 4 5 6 9 3
python3 matching_ref.py 2000 2 3 3 7 4
for mut in noG1 no1P no1F s+1; do python3 matching_ref.py 3000 3 5 5 9 5 $mut; done
python3 matching_ref.py 4000 3 5 5 9 6 extP   # strengthening: Ext over F ∪ P (expected to hold)
