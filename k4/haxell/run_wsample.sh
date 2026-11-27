#!/bin/sh
# Conjecture W at sampled states of random instances with n = 6-8 (k4/haxell.md §7); logs in results/k4_haxell/
cd "$(dirname "$0")"
L=../../results/k4_haxell
python3 ht_wsample.py 400 11 6 10 4 START=8 LEN=30 > $L/wsample_n6m10k4.log 2>&1
python3 ht_wsample.py 400 12 6 11 5 START=8 LEN=30 > $L/wsample_n6m11k5.log 2>&1
python3 ht_wsample.py 300 13 7 12 4 START=8 LEN=30 > $L/wsample_n7m12k4.log 2>&1
python3 ht_wsample.py 300 14 7 13 5 START=8 LEN=30 > $L/wsample_n7m13k5.log 2>&1
python3 ht_wsample.py 200 15 8 14 4 START=8 LEN=30 > $L/wsample_n8m14k4.log 2>&1
python3 ht_wsample.py 200 16 8 15 5 START=8 LEN=30 > $L/wsample_n8m15k5.log 2>&1
python3 ht_wsample.py 300 17 6 10 4 START=8 LEN=30 VMAX=4 > $L/wsample_n6m10k4_ties.log 2>&1
python3 ht_wsample.py 300 18 7 12 5 START=8 LEN=30 VMAX=4 > $L/wsample_n7m12k5_ties.log 2>&1
echo ALLDONE > $L/wsample_done.flag
