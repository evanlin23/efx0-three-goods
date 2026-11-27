#!/bin/sh
# augmentation-radius census (k4/haxell.md §3.5); logs in results/k4_haxell/
cd "$(dirname "$0")"
L=../../results/k4_haxell
python3 ht_aug.py special NMAX=4 MMAX=8 DMAX=4 SHOW=3 > $L/aug_special.log 2>&1
python3 ht_aug.py gen:3000:14:2:5:4 NMAX=2 MMAX=8 DMAX=4 SHOW=4 > $L/aug_gen_n2m5k4.log 2>&1
python3 ht_aug.py gen:3000:15:2:5:5 NMAX=2 MMAX=8 DMAX=4 SHOW=4 > $L/aug_gen_n2m5k5.log 2>&1
python3 ht_aug.py gen:3000:13:2:5:3 NMAX=2 MMAX=8 DMAX=4 SHOW=4 > $L/aug_gen_n2m5k3.log 2>&1
python3 ht_aug.py gen:2000:26:2:6:6 NMAX=2 MMAX=8 DMAX=4 SHOW=4 > $L/aug_gen_n2m6k6.log 2>&1
python3 ht_aug.py screen NMAX=4 MMAX=7 DMAX=4 SHOW=6 > $L/aug_screen.log 2>&1
python3 ht_aug.py cores:k4_certs_2.json.gz,k4_certs_3.json.gz:1500:7 NMAX=3 MMAX=7 DMAX=4 SHOW=4 > $L/aug_cores_n3.log 2>&1
python3 ht_aug.py gen:800:34:3:6:4 NMAX=3 MMAX=8 DMAX=4 SHOW=4 > $L/aug_gen_n3m6k4.log 2>&1
python3 ht_aug.py gen:800:33:3:6:3 NMAX=3 MMAX=8 DMAX=4 SHOW=4 > $L/aug_gen_n3m6k3.log 2>&1
echo ALLDONE > $L/aug_done.flag
