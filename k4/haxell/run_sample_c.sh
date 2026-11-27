#!/bin/sh
# random samples through the C census (k4/haxell.md §4), replacing the slow Python samples at m >= 7
cd "$(dirname "$0")"
L=../../results/k4_haxell
for k in 4 7; do python3 gstar_run.py gen:20000:7$k:2:7:$k NMAX=2 MMAX=8 SHOW=4 > $L/gstarc_gen_n2m7k$k.log 2>&1; done
for k in 4 8; do python3 gstar_run.py gen:10000:8$k:2:8:$k NMAX=2 MMAX=8 SHOW=4 > $L/gstarc_gen_n2m8k$k.log 2>&1; done
for m in 5 6 7; do for k in 3 4; do python3 gstar_run.py gen:5000:9$m$k:3:$m:$k NMAX=3 MMAX=8 SHOW=4 > $L/gstarc_gen_n3m${m}k$k.log 2>&1; done; done
python3 gstar_run.py gen:3000:96:3:8:3 NMAX=3 MMAX=8 SHOW=4 > $L/gstarc_gen_n3m8k3.log 2>&1
python3 gstar_run.py gen:3000:97:3:8:4 NMAX=3 MMAX=8 SHOW=4 > $L/gstarc_gen_n3m8k4.log 2>&1
python3 gstar_run.py gen:1000:98:4:7:3 NMAX=4 MMAX=8 SHOW=4 > $L/gstarc_gen_n4m7k3.log 2>&1
python3 gstar_run.py gen:1000:99:4:7:4 NMAX=4 MMAX=8 SHOW=4 > $L/gstarc_gen_n4m7k4.log 2>&1
echo ALLDONE > $L/samplec_done.flag
