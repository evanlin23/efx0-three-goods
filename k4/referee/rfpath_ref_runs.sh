#!/bin/sh
# Referee runs for Lemma RF-PATH (k4/girth.md §7, 8f7ba8aa) and Lemma RF-ROT (k4/ttc.md §14.7, d451ea0c).
cd "$(dirname "$0")"
python3 rfpath_ref.py 400000 1 4
python3 rfpath_ref.py 400000 2 12
# generalized RF-PATH (any receiver u), girth 712a5688; and the mutation u frozen (must fail)
python3 rfpath_ref.py 400000 3 4 receiver
python3 rfpath_ref.py 400000 4 12 receiver
python3 rfpath_ref.py 100000 5 4 frozen
