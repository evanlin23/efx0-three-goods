#!/bin/sh
# W^sub with welfare and with leximin together on the n = 4, k = 4 cores (ht_n4core.py), as run_n4core.sh.
cd "$(dirname "$0")"
L=../../results/k4_haxell
M=2,1,1,1,0,0,0,2
python3 ht_n4core.py MODE=all MMAX=5 PMAX=62208 PROCS=2 MARGS=$M > $L/n4core_wl_all_m5.log 2>&1
python3 ht_n4core.py MODE=all MMIN=4 MMAX=4 PMAX=3000000 PROCS=2 MARGS=$M > $L/n4core_wl_all_m4.log 2>&1
python3 ht_n4core.py MODE=sample N=200 MMIN=4 MMAX=8 SEED=1 PROCS=2 MARGS=$M > $L/n4core_wl_sample_cert.log 2>&1
python3 ht_n4core.py MODE=sample N=100 MMIN=4 MMAX=8 SEED=2 SCALE=1 DOMAIN=strict PROCS=2 MARGS=$M > $L/n4core_wl_sample_strict_scaled.log 2>&1
python3 ht_n4core.py MODE=sample N=20 MMIN=9 MMAX=9 SEED=3 PROCS=2 MARGS=$M > $L/n4core_wl_sample_m9.log 2>&1
echo ALLDONE > $L/n4core_wl_done.flag
