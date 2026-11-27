#!/bin/sh
# one-step-lemma candidates for CONN_2 (k4/haxell.md §6); logs in results/k4_haxell/
cd "$(dirname "$0")"
L=../../results/k4_haxell
cc -O2 -o gstar_measure gstar_measure.c 2>/dev/null
python3 gstar_measure_run.py screen NMAX=4 MMAX=7 MAXSTATES=400000 > $L/measure_screen.log 2>&1
python3 gstar_measure_run.py gen:800:33:3:6:3 NMAX=3 MMAX=6 > $L/measure_gen_n3m6k3.log 2>&1
python3 gstar_measure_run.py gen:800:34:3:6:4 NMAX=3 MMAX=6 > $L/measure_gen_n3m6k4.log 2>&1
python3 gstar_measure_run.py gen:3000:15:2:5:5 NMAX=2 MMAX=6 > $L/measure_gen_n2m5k5.log 2>&1
python3 gstar_measure_run.py cores:k4_certs_2.json.gz,k4_certs_3.json.gz:600:7 NMAX=3 MMAX=7 > $L/measure_cores_n3.log 2>&1
python3 gstar_measure_run.py ext NMAX=5 MMAX=9 MAXSTATES=11000000 > $L/measure_ext.log 2>&1
echo ALLDONE > $L/measure_done.flag
