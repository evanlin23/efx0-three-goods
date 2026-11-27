#!/bin/sh
# The Pareto form of the set-move lemma on the n = 4, k = 4 cores (ht_n4core.py): P^sub is ordinal, so every sampled type
# profile is an exact test of that profile.  Two moves (how often do they fail on cores?) and three moves (P^sub_3).
cd "$(dirname "$0")"
L=../../results/k4_haxell
python3 ht_n4core.py MODE=sample N=200 MMIN=4 MMAX=8 SEED=11 PROCS=2 MARGS=2,1,19,1 > $L/n4core_p2_sample_cert.log 2>&1
python3 ht_n4core.py MODE=sample N=200 MMIN=4 MMAX=8 SEED=11 PROCS=2 MARGS=3,1,19,1 > $L/n4core_p3_sample_cert.log 2>&1
echo ALLDONE > $L/p3cores_done.flag
