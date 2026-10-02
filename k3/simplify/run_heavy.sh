#!/bin/bash
# K3S heavy tests (logged under results/k3_simplify/)
cd "$(dirname "$0")"
L=../../results/k3_simplify
{ time python3 test_k3s.py cores 5 ; } > $L/k3s_cores_5.log 2>&1
{ time python3 test_k3s.py small 4 6 ; } > $L/k3s_small_4_6.log 2>&1
{ time python3 test_k3s.py rprof 2000000 7 ; } > $L/k3s_rprof.log 2>&1
{ time python3 test_k3s.py random 2000000 5 ; } > $L/k3s_random.log 2>&1
{ time python3 test_k3s.py sd2 1000000 9 ; } > $L/k3s_sd2.log 2>&1
{ time python3 test_k3s.py small 4 7 ; } > $L/k3s_small_4_7.log 2>&1
