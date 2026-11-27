#!/bin/sh
# G* trap census (k4/haxell.md §3.4); logs in results/k4_haxell/
cd "$(dirname "$0")"
L=../../results/k4_haxell
export GSTAR_PAR=1
python3 ht_gstar.py screen NMAX=4 MMAX=8 SHOW=12 > $L/gstar_screen.log 2>&1
python3 ht_gstar.py suite NMAX=4 MMAX=8 SHOW=12 > $L/gstar_suite.log 2>&1
python3 ht_gstar.py special NMAX=4 MMAX=8 SHOW=12 > $L/gstar_special.log 2>&1
python3 ht_gstar.py cores:k4_certs_2.json.gz,k4_certs_3.json.gz:1500:7 NMAX=3 MMAX=8 SHOW=12 > $L/gstar_cores_n3.log 2>&1
for k in 3 4 5; do python3 ht_gstar.py gen:3000:1$k:2:5:$k NMAX=2 MMAX=8 SHOW=6 > $L/gstar_gen_n2m5k$k.log 2>&1; done
for k in 3 4 6; do python3 ht_gstar.py gen:2000:2$k:2:6:$k NMAX=2 MMAX=8 SHOW=6 > $L/gstar_gen_n2m6k$k.log 2>&1; done
for k in 3 4 6; do python3 ht_gstar.py gen:800:3$k:3:6:$k NMAX=3 MMAX=8 SHOW=6 > $L/gstar_gen_n3m6k$k.log 2>&1; done
for k in 3 4 7; do python3 ht_gstar.py gen:300:4$k:3:7:$k NMAX=3 MMAX=8 SHOW=6 > $L/gstar_gen_n3m7k$k.log 2>&1; done
