#!/bin/sh
# P^sub (two moves) and P^sub_3 (three moves) on the n = 4, k = 4 cores, with every strict type allowed (balanced or
# not: DOMAIN=strict), 100 random profiles per core with 4 <= m <= 8.  Each profile is an exact test (P^sub is ordinal).
cd "$(dirname "$0")"
L=../../results/k4_haxell
python3 ht_n4core.py MODE=sample N=100 MMIN=4 MMAX=8 SEED=12 DOMAIN=strict PROCS=2 MARGS=2,1,19,1 > $L/n4core_p2_sample_strict.log 2>&1
python3 ht_n4core.py MODE=sample N=100 MMIN=4 MMAX=8 SEED=12 DOMAIN=strict PROCS=2 MARGS=3,1,19,1 > $L/n4core_p3_sample_strict.log 2>&1
echo ALLDONE > $L/p3strict_done.flag
