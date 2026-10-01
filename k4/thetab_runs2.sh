#!/bin/sh
# Further runs of k4/thetab.md §4 (after k4/thetab_runs.sh): random n = 3 profiles of every certified core (Corollary
# N3 asserted at every state in setting (H)), the twin hunts (many T3-stage states in (H)), and the replay of the failed
# candidates with two implementations. One worker, sequential.
set -e
R=results/k4_thetab
mkdir -p $R
run() { out=$R/$1.log; shift; [ -s $out ] && return 0; python3 "$@" > $out.tmp && mv $out.tmp $out; }
run scan_certs_3_r500 k4/thetab_scan.py certs results/k4_certs_3.json.gz --rand=500 --seed=7
for s in 1 2; do
  run scan_twin_s$s k4/thetab_scan.py twin $s 1000000 --nmin=4 --nmax=5 --tlim=900
done
run attempts attempts/k4_thetab_attempts.py
