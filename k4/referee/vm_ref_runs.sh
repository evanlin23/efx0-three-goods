#!/bin/sh
# Referee runs for Theorem VM; log: results/k4_referee/vm_ref.log
cd "$(dirname "$0")/../.."
P=k4/referee/vm_ref.py
{
python3 $P lit
python3 $P exh 2 3 3
python3 $P exh 3 3 2
python3 $P exh 2 4 3
python3 $P exh 2 5 2
python3 $P exh 3 4 2
python3 $P exh 2 6 2 2000
python3 $P rand 20000 4 7 6 1 3000
python3 $P rand 20000 6 10 9 2 500
python3 $P cont 20000 3 3000
python3 $P cont 20000 4 3000
} > results/k4_referee/vm_ref.log 2>&1
