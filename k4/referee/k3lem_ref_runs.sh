#!/bin/sh
# Referee runs for k3-oc1 Lemmas 4-7 (k4/k3_oc1.md §12 at 9719be2) and kgen-n3 G5 / G5' (kgen/n3.md §15.6 at a319483).
cd "$(dirname "$0")"
python3 k3lem_ref.py named
python3 k3lem_ref.py rand 150000 1 &
python3 k3lem_ref.py rand 150000 2 &
python3 k3lem_ref.py rand 60000 3 anychain &
wait
