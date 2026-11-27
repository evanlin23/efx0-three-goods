#!/bin/sh
# Referee runs for Theorem R1C; log: results/k4_referee/k3oc1_ref.log
cd "$(dirname "$0")/../.."
P=k4/referee/k3oc1_ref.py
{
python3 $P exh3 4 oc1
python3 $P exh3 5 oc1
python3 $P exh3 6 oc1
python3 $P rand 20000 4 5 8 11 oc1
python3 $P rand 5000 5 6 9 12 oc1
python3 $P rand 3000 5 7 10 13 oc1
python3 $P rand 400 6 7 10 14 oc1
python3 $P rand 300 6 8 12 15
} > results/k4_referee/k3oc1_ref.log 2>&1
