#!/bin/sh
# Referee runs for CH-A, CH-B; log: results/k4_referee/charity_ref.log
cd "$(dirname "$0")/../.."
P=k4/referee/charity_ref.py
{
python3 $P family 5 3
python3 $P family 4 4
python3 $P packing 3 5 | head -1
python3 $P packing 4 3 | head -1
python3 $P packing 5 2 | head -1
python3 $P states 400 3 4 4 6 3 2
python3 $P states 150 3 4 5 7 4 3
} > results/k4_referee/charity_ref.log 2>&1
