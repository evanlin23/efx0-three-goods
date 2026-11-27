#!/bin/sh
# Referee runs for Theorem B* and Lemmas 1, 3 (k3_oc1.md); log: results/k4_referee/k3oc1_ref_bstar.log
cd "$(dirname "$0")/../.."
P=k4/referee/k3oc1_ref.py
{
python3 $P bstar 20000 4 5 8 31
python3 $P bstar 4000 5 6 10 32
python3 $P bstar 300 6 7 12 33
python3 $P lem13 20000 3 4 7 34
python3 $P lem13 20000 4 5 9 35
python3 $P lem13 10000 5 6 10 36
} > results/k4_referee/k3oc1_ref_bstar.log 2>&1
