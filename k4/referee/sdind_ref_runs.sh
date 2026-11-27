#!/bin/sh
# Referee runs for Lemmas D, F, S, U, BOTH-TP, Corollary TP; log: results/k4_referee/sdind_ref.log
cd "$(dirname "$0")/../.."
P=k4/referee/sdind_ref.py
{
python3 $P ucex
python3 $P run 5000 3 4 4 8 11
python3 $P run 1500 5 5 5 9 12
python3 $P run 3000 2 3 3 7 13
} > results/k4_referee/sdind_ref.log 2>&1
