#!/bin/sh
# Phase 1 validation of k4/cover_check.py on PR #80's and PR #82's inputs (workstream compute/k4-cover).
# Needs PR #80's files in k4/suite/.cache/sx/ (see k4/cover_check.py). Resumable: each output is its own checkpoint.
S=k4/suite/.cache/sx/results/k4_sx
V=results/k4_cover/validate
mkdir -p $V
case "$1" in
n3)    python3 k4/cover_check.py $V/f1_n3_all.jsonl.gz $S/hunt/n3_all_*.jsonl.gz > $V/f1_n3_all.log 2>&1 ;;
n4a)   python3 k4/cover_check.py $V/f1_n4_hunts_p0.jsonl.gz $S/hunt/n4_3_r40k.jsonl.gz $S/hunt/n4_pure_r40k.jsonl.gz $S/hunt/n4_pure_r400k.jsonl.gz --part=0/2 > $V/f1_n4_hunts_p0.log 2>&1 ;;
n4b)   python3 k4/cover_check.py $V/f1_n4_hunts_p1.jsonl.gz $S/hunt/n4_3_r40k.jsonl.gz $S/hunt/n4_pure_r40k.jsonl.gz $S/hunt/n4_pure_r400k.jsonl.gz --part=1/2 > $V/f1_n4_hunts_p1.log 2>&1 ;;
n5)    python3 k4/cover_check.py $V/f1_n5_hunts.jsonl.gz $S/hunt/n5_pure_r1000_*.jsonl.gz --indep=1 > $V/f1_n5_hunts.log 2>&1 ;;
rc)    python3 k4/cover_check.py $V/f1_rc45.jsonl.gz inst:$S/rc/rc_fail_inst.json --indep=9 > $V/f1_rc45.log 2>&1 ;;
stuck1) python3 k4/cover_check.py $V/f1_t1stuck.jsonl.gz $S/t3stage/keys.jsonl.gz --fmax=1 > $V/f1_t1stuck.log 2>&1 ;;
cat)   python3 k4/cover_check.py $V/f2_cat.jsonl.gz --nodedup $S/chunks/gap_n4_3_s4000@f2e1_c000.jsonl.gz $S/chunks/gap_n4_pure_s4000@f2e1_c000.jsonl.gz \
         $S/chunks/hard_hunt@f2e1_c000.jsonl.gz $S/chunks/hunt_n4_3_s400k@f2e1_c000.jsonl.gz $S/chunks/hunt_n4_pure_s400k@f2e1_c000.jsonl.gz \
         $S/chunks/gap_n4_1_c0??.jsonl.gz --fmin=2 > $V/f2_cat.log 2>&1 ;;
stuck2) python3 k4/cover_check.py $V/f2_t1stuck.jsonl.gz $S/t3stage/keys.jsonl.gz --fmin=2 > $V/f2_t1stuck.log 2>&1 ;;
n5c)   python3 k4/cover_check.py $V/f2_n5c.jsonl.gz inst:$S/f2/rt4_n5c_inst.json --indep=1 > $V/f2_n5c.log 2>&1 ;;
esac
