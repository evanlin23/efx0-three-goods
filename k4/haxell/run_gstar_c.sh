#!/bin/sh
# G* trap census with the C implementation (k4/haxell.md §3.4); logs in results/k4_haxell/
cd "$(dirname "$0")"
L=../../results/k4_haxell
cc -O2 -o gstar gstar.c
python3 gstar_run.py screen NMAX=4 MMAX=7 XCHECK=1 SHOW=0 > $L/gstarc_xcheck_screen.log 2>&1
python3 gstar_run.py suite NMAX=4 MMAX=7 XCHECK=1 SHOW=0 > $L/gstarc_xcheck_suite.log 2>&1
python3 gstar_run.py special NMAX=5 MMAX=9 SHOW=8 > $L/gstarc_special.log 2>&1
python3 gstar_run.py screen NMAX=5 MMAX=10 SHOW=12 > $L/gstarc_screen.log 2>&1
python3 gstar_run.py suite NMAX=5 MMAX=10 SHOW=12 > $L/gstarc_suite.log 2>&1
python3 gstar_run.py logs NMAX=5 MMAX=10 SHOW=12 > $L/gstarc_logs.log 2>&1
python3 gstar_run.py cores:k4_certs_4_n4_1.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz,k4_certs_4_pure.json.gz:300:9 NMAX=4 MMAX=9 SHOW=8 > $L/gstarc_cores_n4.log 2>&1
python3 gstar_run.py gen:300:51:4:8:3 NMAX=4 MMAX=9 SHOW=8 > $L/gstarc_gen_n4m8k3.log 2>&1
python3 gstar_run.py gen:300:52:4:8:4 NMAX=4 MMAX=9 SHOW=8 > $L/gstarc_gen_n4m8k4.log 2>&1
python3 gstar_run.py gen:200:53:4:8:8 NMAX=4 MMAX=9 SHOW=8 > $L/gstarc_gen_n4m8k8.log 2>&1
python3 gstar_run.py gen:150:54:5:8:3 NMAX=5 MMAX=9 SHOW=8 > $L/gstarc_gen_n5m8k3.log 2>&1
python3 gstar_run.py gen:150:55:5:8:4 NMAX=5 MMAX=9 SHOW=8 > $L/gstarc_gen_n5m8k4.log 2>&1
python3 gstar_run.py gen:600:56:3:9:3 NMAX=3 MMAX=10 SHOW=8 > $L/gstarc_gen_n3m9k3.log 2>&1
python3 gstar_run.py gen:600:57:3:9:4 NMAX=3 MMAX=10 SHOW=8 > $L/gstarc_gen_n3m9k4.log 2>&1
echo ALLDONE > $L/gstarc_done.flag
