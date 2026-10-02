#!/bin/sh
# Phase 2 of workstream compute/k4-zmove: k4/zmove_check.py on every input compute/k4-cover used, one output per run
# (each output is its own checkpoint: rerunning a name resumes it). Usage: sh k4/zmove_runs.sh NAME
# Needs PR #80's files in k4/suite/.cache/sx/ (see k4/zmove_check.py).
O=results/k4_zmove/phase2
C=results/k4_cover
SX=k4/suite/.cache/sx/results/k4_sx
mkdir -p $O
run() {  # name args...
  n=$1; shift
  python3 k4/zmove_check.py $O/$n.jsonl.gz "$@" >> $O/$n.log 2>&1
}
case "$1" in
# every strict profile of every n = 3 core with a key of def* > 0 (compute/k4-cover's screen; all f)
n3)       run n3_all $C/screen/n3_all.jsonl.gz --indep=10 ;;
# n = 4 cores: one 4-good agent (every profile), three 4-good agents and pure (random samples screened)
n4)       run n4_1_all $C/screen/n4_1_all.jsonl.gz --indep=1
          run n4_pure_r2k $C/screen/n4_pure_r2k.jsonl.gz --indep=1
          run n4_3_r200k $C/screen/n4_3_r200k.jsonl.gz --indep=10
          run n4_pure_r200k $C/screen/n4_pure_r200k.jsonl.gz --indep=10 ;;
# n = 5 samples: compute/k4-cover's screen and this workstream's new screens (results/k4_zmove/screen/)
n5)       run n5_screens $C/screen/n5_n4_2_r200.jsonl.gz results/k4_zmove/screen/n5_*.jsonl.gz --indep=5 ;;
# every strict profile of every n = 4 core with two 4-good agents (k4/zmove_screens.sh n4_2)
n4_2)     run n4_2_all results/k4_zmove/screen/n4_2_all.jsonl.gz --indep=10 ;;
# the explicit profiles of compute/k4-rt4, k4-dl13, k4-rc, k4-portfolio (k4/cover_inputs.py): f >= 2 and f = 1
dumps2)   run dumps_f2_p$2 $C/inputs/dumps_f2.jsonl.gz --maxn=6 --part=$2/4 --indep=20 ;;
dumps2n7) run dumps_f2_n7 $C/inputs/dumps_f2.jsonl.gz --minn=7 --indep=0 ;;
rest5)    run dumps_f2_rest_n5_p$2 $C/inputs/dumps_f2_rest_n5.jsonl.gz --part=$2/2 --indep=20 ;;
n6s)      run dumps_f2_n6_sample8 $C/inputs/dumps_f2_n6_sample8.jsonl.gz --indep=25 ;;
dumps1)   run dumps_f1 results/k4_zmove/inputs/dumps_f1.jsonl.gz --indep=5 ;;
suite)    run suite results/k4_zmove/inputs/suite.jsonl.gz --maxn=6 --indep=1 ;;
# compute/k4-cover's hunt dumps
hunts4)   run hunt_f2x2_n4_m10 $C/hunt/f2x2_n4_m10.jsonl.gz $C/hunt/first_f2x2_1min.jsonl.gz --indep=20
          run hunt_f1 $C/hunt/f1_seed0.jsonl.gz $C/hunt/f1_seed9.jsonl.gz $C/hunt/f1seed0_anyf.jsonl.gz --indep=10 ;;
hunt5)    run hunt_unc5_p$2 $C/hunt/unc5_seed0.jsonl.gz --part=$2/2 --indep=40 ;;
# PR #80's and PR #82's inputs (compute/k4-cover Phase 1)
validate) run val_f1_n4_hunts $SX/hunt/n4_3_r40k.jsonl.gz $SX/hunt/n4_pure_r40k.jsonl.gz $SX/hunt/n4_pure_r400k.jsonl.gz --indep=10
          run val_f1_n5_hunts $SX/hunt/n5_pure_r1000_*.jsonl.gz --indep=1
          run val_f1_rc45 inst:$SX/rc/rc_fail_inst.json --indep=1
          run val_t1stuck $SX/t3stage/keys.jsonl.gz --indep=10
          run val_f2_cat $SX/chunks/gap_n4_3_s4000@f2e1_c000.jsonl.gz $SX/chunks/gap_n4_pure_s4000@f2e1_c000.jsonl.gz \
            $SX/chunks/hard_hunt@f2e1_c000.jsonl.gz $SX/chunks/hunt_n4_3_s400k@f2e1_c000.jsonl.gz \
            $SX/chunks/hunt_n4_pure_s400k@f2e1_c000.jsonl.gz $SX/chunks/gap_n4_1_c0??.jsonl.gz --indep=1
          run val_f2_n5c inst:$SX/f2/rt4_n5c_inst.json --indep=1 ;;
# full cross-check on a stratified sample (every K-th distinct profile of each input) with k4/zmove_indep.py's repairing
# move counts and best per maximum compared as well (results/k4_zmove/xcheck/)
xcheck)   X=results/k4_zmove/xcheck; mkdir -p $X
          python3 k4/zmove_check.py $X/n3.jsonl.gz $C/screen/n3_all.jsonl.gz --part=0/100 --indep=1 >> $X/n3.log 2>&1
          python3 k4/zmove_check.py $X/n4.jsonl.gz $C/screen/n4_3_r200k.jsonl.gz $C/screen/n4_pure_r200k.jsonl.gz --part=0/10 --indep=1 >> $X/n4.log 2>&1
          python3 k4/zmove_check.py $X/dumps_f2.jsonl.gz $C/inputs/dumps_f2.jsonl.gz --maxn=6 --part=1/40 --indep=1 >> $X/dumps_f2.log 2>&1
          python3 k4/zmove_check.py $X/dumps_f1.jsonl.gz results/k4_zmove/inputs/dumps_f1.jsonl.gz --part=1/10 --indep=1 >> $X/dumps_f1.log 2>&1
          python3 k4/zmove_check.py $X/hunts.jsonl.gz $C/hunt/f2x2_n4_m10.jsonl.gz $C/hunt/unc5_seed0.jsonl.gz --part=1/50 --indep=1 >> $X/hunts.log 2>&1 ;;
esac
