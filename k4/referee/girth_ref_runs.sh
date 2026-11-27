#!/bin/sh
# Referee runs for Theorem T1 and Lemmas SINK, PARK, SLACK; log: results/k4_referee/girth_ref.log
cd "$(dirname "$0")/../.."
P=k4/referee/girth_ref.py
{
python3 $P t1 20000 3 7 3 10 4 4 add 11
python3 $P t1 20000 3 7 3 10 4 4 mono 12
python3 $P t1 5000 5 9 6 14 4 6 add 13
python3 $P t1 5000 5 9 6 14 4 6 mono 14
GIRTH_BAD0=1 python3 $P t1 3000 3 6 4 9 4 4 add 15
python3 $P park 2000 3 5 3 7 3 4 add 16
python3 $P park 2000 3 5 3 7 3 4 mono 17
python3 $P park 500 4 6 5 8 4 4 add 18
python3 $P park 500 4 6 5 8 4 4 mono 19
} > results/k4_referee/girth_ref.log 2>&1
# Lemma ORD and Lemma RF-T-A (k4/girth.md §7 at 56941dc6); run from the repository root; the log keeps 3 of the
# COUNTEREXAMPLE lines (one is printed per core where one occurs)
python3 k4/referee/rft_ref.py 300 2 4 > results/k4_referee/rft_ref_300.log
