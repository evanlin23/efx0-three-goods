#!/bin/sh
# one-step-lemma candidates with steps of up to three local moves (k4/haxell.md §6); logs in results/k4_haxell/
cd "$(dirname "$0")"
L=../../results/k4_haxell
cc -O2 -o gstar_measure gstar_measure.c 2>/dev/null
python3 gstar_measure_run.py gen:800:33:3:6:3 NMAX=3 MMAX=6 RADIUS=3 > $L/measure3_gen_n3m6k3.log 2>&1
python3 gstar_measure_run.py gen:800:34:3:6:4 NMAX=3 MMAX=6 RADIUS=3 > $L/measure3_gen_n3m6k4.log 2>&1
python3 gstar_measure_run.py gen:3000:15:2:5:5 NMAX=2 MMAX=6 RADIUS=3 > $L/measure3_gen_n2m5k5.log 2>&1
python3 gstar_measure_run.py gen:3000:13:2:5:3 NMAX=2 MMAX=6 RADIUS=3 > $L/measure3_gen_n2m5k3.log 2>&1
python3 gstar_measure_run.py cores:k4_certs_2.json.gz,k4_certs_3.json.gz:600:7 NMAX=3 MMAX=7 RADIUS=3 > $L/measure3_cores_n3.log 2>&1
python3 gstar_measure_run.py suite NMAX=4 MMAX=7 MAXSTATES=400000 RADIUS=3 > $L/measure3_suite.log 2>&1
python3 gstar_measure_run.py ext NMAX=5 MMAX=9 MAXSTATES=11000000 RADIUS=3 > $L/measure3_ext.log 2>&1
python3 gstar_measure_run.py gen:600:55:3:7:5 NMAX=3 MMAX=7 RADIUS=3 > $L/measure3_gen_n3m7k5.log 2>&1
python3 gstar_measure_run.py gen:300:57:4:7:4 NMAX=4 MMAX=7 RADIUS=3 > $L/measure3_gen_n4m7k4.log 2>&1
python3 gstar_measure_run.py gen:300:58:4:7:7 NMAX=4 MMAX=7 RADIUS=3 > $L/measure3_gen_n4m7k7.log 2>&1
python3 gstar_measure_run.py ttc NMAX=5 MMAX=9 MAXSTATES=11000000 RADIUS=3 > $L/measure3_ttc.log 2>&1
echo ALLDONE > $L/measure3_done.flag
