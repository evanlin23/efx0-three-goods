#!/bin/sh
# Model G victim-free search from every serial-dictatorship start (k4/haxell.md §3.1); logs in results/k4_haxell/
cd "$(dirname "$0")"
L=../../results/k4_haxell
python3 ht_bfs.py suite NMAX=5 MODEL=G CAP=200000 > $L/bfs_suite_G.log 2>&1
python3 ht_bfs.py special NMAX=5 MODEL=G CAP=200000 > $L/bfs_special_G.log 2>&1
python3 ht_bfs.py logs NMAX=4 MODEL=G CAP=200000 > $L/bfs_logs_G.log 2>&1
python3 ht_bfs.py cores:k4_certs_4_n4_1.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz,k4_certs_4_pure.json.gz:500:11 NMAX=4 MODEL=G CAP=200000 > $L/bfs_cores_n4_G.log 2>&1
python3 ht_bfs.py cores:k4_certs_5_n4_1.json.gz,k4_certs_5_n4_2.json.gz:60:12 NMAX=5 MODEL=G CAP=200000 > $L/bfs_cores_n5_G.log 2>&1
echo ALLDONE > $L/bfsmore_done.flag
