#!/usr/bin/env bash
# Every log of k4/lemmam_bt.md (results/k4_lemmam_bt/), one worker, steps in sequence. classes, rkall and exact are
# resumable (they skip the first agents their log already has). Usage: bash k4/lemmam_bt_runs.sh [STEP ...]
# Steps: core (and Lemmas 1, 2 of §3 on HH_3, HH_4), classes (Lemma K, this workstream's implementation), rk (k4/rulef.c
# of PR #72 on H_3 + q: the first big-top agent and rule RK; $RULEF_SRC if rulef.c is not at k4/rulef.c), rkall
# (k4/rulef.c's classes of every first agent of HH_3, one per run; not in the default steps: over five minutes per
# first agent), exactA, exactB (LB4r with <= 1 rotation, PR #33's
# encodings A and B), d2 (K4.D on HH_3).
set -u
cd "$(dirname "$0")/.."
R=results/k4_lemmam_bt; mkdir -p $R
P="python3 k4/lemmam_bt_hh.py"
steps=${*:-core classes rk d2 exactA exactB}
for s in $steps; do case $s in
core)    { $P core Hq3; $P core HH3; $P core HH2; } > $R/core.log
         { $P lemmas HH3; $P lemmas HH4; } > $R/lemmas.log ;;
classes) $P classes Hq3 13 --log=$R/classes_Hq3.log > /dev/null
         $P classes HH3 --log=$R/classes_HH3.log > /dev/null ;;
rk)      $P rk Hq3 > $R/rk_Hq3.log ;;
rkall)   $P rkall HH3 --log=$R/rk_HH3.log > /dev/null ;;
exactA)  $P exact Hq3 A 13 --log=$R/exactA_Hq3.log > /dev/null
         $P exact HH3 A --log=$R/exactA_HH3.log > /dev/null ;;
exactB)  $P exact Hq3 B 13 --log=$R/exactB_Hq3.log > /dev/null
         $P exact HH3 B --log=$R/exactB_HH3.log > /dev/null ;;
d2)      $P d2 HH3 > $R/d2_HH3.log ;;
esac; done
