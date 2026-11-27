#!/bin/sh
# full G* census at k >= 5 on random instances (k4/haxell.md §5); runs after run_pw.sh
cd "$(dirname "$0")"
L=../../results/k4_haxell
while [ ! -f $L/pw_done.flag ]; do sleep 20; done
for k in 5 6 7 8; do python3 gstar_run.py gen:2000:6$k:3:8:$k NMAX=3 MMAX=10 SHOW=6 > $L/gstarc_gen_n3m8k$k.log 2>&1; done
for k in 5 7 10; do python3 gstar_run.py gen:800:7$k:3:10:$k NMAX=3 MMAX=10 SHOW=6 > $L/gstarc_gen_n3m10k$k.log 2>&1; done
for k in 5 6 8; do python3 gstar_run.py gen:600:8$k:4:8:$k NMAX=4 MMAX=10 SHOW=6 > $L/gstarc_gen_n4m8k$k.log 2>&1; done
for k in 5 6 9; do python3 gstar_run.py gen:150:9$k:4:9:$k NMAX=4 MMAX=10 SHOW=6 > $L/gstarc_gen_n4m9k$k.log 2>&1; done
for k in 5 8; do python3 gstar_run.py gen:200:5$k:5:8:$k NMAX=5 MMAX=10 SHOW=6 > $L/gstarc_gen_n5m8k$k.log 2>&1; done
echo ALLDONE > $L/highk_done.flag
