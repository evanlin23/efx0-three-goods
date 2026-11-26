#!/bin/sh
# Referee runs for Lemma 2 / 2*, Corollary 2.1, Proposition 3, Theorem F1_1; log: results/k4_referee/oc1hall_ref.log
cd "$(dirname "$0")/../.."
P=k4/referee/oc1hall_ref.py
{
python3 $P run 3000 3 4 4 8 strict 11
python3 $P run 3000 3 4 4 8 ties 12
python3 $P run 600 5 5 6 9 strict 13
python3 $P f1 1500 3 5 5 9 strict 14
python3 $P f1 1500 3 5 5 9 ties 15
python3 $P f1b3 1000 3 5 strict 16
python3 $P f1b3 1000 3 5 ties 17
} > results/k4_referee/oc1hall_ref.log 2>&1
