#!/bin/sh
# The chain lemma and augmenting chains (ht_chain.py, ht_rescue.py; k4/haxell.md §6 "Alternating chains"): every
# strict type profile at n = 2 (k <= 4) and n = 3 (k <= 3); every state of the 44 two-move-failure instances; random
# type profiles of the n = 4, k = 4 cores.
cd "$(dirname "$0")/../.."
L=results/k4_haxell
python3 k4/haxell/ht_chain.py GEN=n2 K=4 L=6 AUG=1 > $L/chain_n2_k4.log 2>&1
python3 k4/haxell/ht_chain.py GEN=n3 K=3 MMAX=9 L=6 AUG=1 > $L/chain_n3_k3.log 2>&1
F="$L/wclimb_tight_n4m7k4.log $L/lclimb_seed1_n4m7k4.log $L/lclimb_seed2_n4m7k4.log $L/lclimb_seed4_n4m7k4.log $L/n5climb_r2_s4_m19.log $L/n4core_p2_sample_cert.log"
python3 k4/haxell/ht_rescue.py $F CHAIN=6 > $L/chain_failures.log 2>&1
grep -h '^   instance' $L/rescue_anatomy.log | sed 's/^   instance //' | python3 k4/haxell/ht_chain.py GEN=stdin L=6 AUG=1 > $L/chain_failures_allstates.log 2>&1
python3 k4/haxell/ht_chain.py GEN=cores N=10 MMIN=4 MMAX=7 SEED=41 L=6 AUG=1 > $L/chain_cores_m4to7.log 2>&1
python3 k4/haxell/ht_chain.py GEN=cores N=2 MMIN=8 MMAX=8 SEED=42 L=6 AUG=1 > $L/chain_cores_m8.log 2>&1
echo ALLDONE > $L/chain_done.flag
