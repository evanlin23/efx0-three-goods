#!/bin/sh
# The runs of k4/thetab.md §1, §4, §5 (workstream proof/k4-thetab). One worker, sequential; each run under ~20 minutes.
# Needs #53's catalogues at 245040b in k4/suite/.cache/gapbench (k4/strategy.md §4), PR #75's dumps
# (results/k4_dl13_stuck/, on main), and for the input "rc" PR #80's copy of compute/k4-rc's 45 profiles at ebe244f in
# k4/suite/.cache/sx (see k4/thetab_cover_runs.sh). Logs in results/k4_thetab/. A run whose log exists is skipped
# (delete it to redo).
set -e
R=results/k4_thetab
mkdir -p $R
run() { out=$R/$1.log; shift; [ -s $out ] && return 0; python3 "$@" > $out.tmp && mv $out.tmp $out; }
run targets k4/thetab_targets.py --check
run attempts attempts/k4_thetab_attempts.py
run scan_suite k4/thetab_scan.py suite
run scan_rc k4/thetab_scan.py inst k4/suite/.cache/sx/results/k4_sx/rc/rc_fail_inst.json
run scan_gap_n3 k4/thetab_scan.py catalog gap_n3.json.gz
run scan_hard_hunt k4/thetab_scan.py catalog hard_hunt.json.gz
for c in gap_n4_1 gap_n4_2_s4000 gap_n4_3_s4000 gap_n4_pure_s4000; do
  run scan_${c}_e4 k4/thetab_scan.py catalog $c.json.gz --every=4
done
for c in hunt_n4_2_all hunt_n4_3_s400k hunt_n4_pure_s400k; do
  run scan_${c}_e4 k4/thetab_scan.py catalog $c.json.gz --every=4
done
run scan_twin_s1 k4/thetab_scan.py twin 1 1000000 --nmin=4 --nmax=5 --tlim=900
run scan_hunt_s1 k4/thetab_scan.py hunt 1 1000000 --nmin=4 --nmax=5 --tlim=900
