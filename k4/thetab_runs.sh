#!/bin/sh
# The runs of k4/thetab.md §4 (workstream proof/k4-thetab). One worker, sequential; each run under ~20 minutes.
# Needs #53's catalogues at 245040b in k4/suite/.cache/gapbench (k4/strategy.md §4) and PR #75's dumps
# (results/k4_dl13_stuck/, on main). Logs in results/k4_thetab/. A run whose log exists is skipped (delete it to redo).
set -e
R=results/k4_thetab
mkdir -p $R
run() { out=$R/$1.log; shift; [ -s $out ] && return 0; python3 "$@" > $out.tmp && mv $out.tmp $out; }
run targets k4/thetab_targets.py --check
run scan_suite k4/thetab_scan.py suite
run scan_gap_n3 k4/thetab_scan.py catalog gap_n3.json.gz
run scan_hard_hunt k4/thetab_scan.py catalog hard_hunt.json.gz
for c in gap_n4_1 gap_n4_2_s4000 gap_n4_3_s4000 gap_n4_pure_s4000; do
  run scan_${c}_e4 k4/thetab_scan.py catalog $c.json.gz --every=4
done
for c in hunt_n4_2_all hunt_n4_3_s400k hunt_n4_pure_s400k; do
  run scan_${c}_e4 k4/thetab_scan.py catalog $c.json.gz --every=4
done
for c in gap_n5_1_s100 gap_n5_2_s100 gap_n5_3_s100 gap_n5_4_s100 gap_n5_pure_s100; do
  run scan_${c}_e10 k4/thetab_scan.py catalog $c.json.gz --every=10
done
for s in 1 2 3; do
  run scan_hunt_s$s k4/thetab_scan.py hunt $s 1000000 --nmin=4 --nmax=5 --tlim=1100
done
