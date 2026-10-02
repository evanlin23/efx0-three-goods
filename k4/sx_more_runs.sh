#!/bin/sh
# The remaining runs of k4/sx.md §4 and §6, one process at a time, resumable:
# the key graph on #53's catalogues (f >= 2 records of the n = 4 ones; every record of gap_n3, gap_n4_1, gap_n4_2_s4000),
# Lemma A+ (k4/sx_f2.py) on every f >= 2 profile with a key of def* > 0 found there, and the second implementation
# (k4/sx_xcheck.py) on samples of the dumps.
set -e
# the profiles of the T1-stuck states of k4/dl13.md §1 (every T3-stage state is one of them)
T=results/k4_sx/t3stage
[ -s $T/profiles.json.gz ] || python3 k4/sx_t3stage.py
grep -q '^# time' $T/keys.log 2>/dev/null || python3 k4/sx_keygraph.py inst $T/profiles.json.gz --dump=$T/keys.jsonl.gz > $T/keys.log 2>&1
grep -q '^# time' $T/zprime_f1.log 2>/dev/null || python3 k4/sx_zprime.py $T/profiles_f1.jsonl.gz > $T/zprime_f1.log 2>&1
grep -q '^# time' $T/f2.log 2>/dev/null || python3 k4/sx_f2.py $T/keys.jsonl.gz > $T/f2.log 2>&1
[ -s $T/xcheck.log ] || python3 k4/sx_xcheck.py $T/keys.jsonl.gz --mmax=10 > $T/xcheck.log 2>&1
python3 k4/sx_runs.py hard_hunt@f2e1 gap_n4_3_s4000@f2e1 gap_n4_pure_s4000@f2e1 hunt_n4_pure_s400k@f2e1 \
  hunt_n4_3_s400k@f2e1 gap_n4_1 gap_n4_2_s4000 gap_n3
python3 k4/sx_runs.py --sum > /dev/null
[ -s results/k4_sx/f2/catalogues_f2.log ] || python3 k4/sx_f2.py $(ls results/k4_sx/chunks/*@f2*.jsonl.gz) results/k4_sx/chunks/gap_n4_1_c*.jsonl.gz \
  > results/k4_sx/f2/catalogues_f2.log 2>&1
[ -s results/k4_sx/xcheck_gap_n3.log ] || python3 k4/sx_xcheck.py results/k4_sx/chunks/gap_n3_c*.jsonl.gz > results/k4_sx/xcheck_gap_n3.log 2>&1
[ -s results/k4_sx/xcheck_hunt_n4.log ] || python3 k4/sx_xcheck.py results/k4_sx/hunt/n4_3_r40k.jsonl.gz results/k4_sx/hunt/n4_pure_r40k.jsonl.gz \
  > results/k4_sx/xcheck_hunt_n4.log 2>&1
[ -s results/k4_sx/xcheck_hunt_n3.log ] || python3 k4/sx_xcheck.py results/k4_sx/hunt/n3_all_10.jsonl.gz results/k4_sx/hunt/n3_all_20.jsonl.gz \
  results/k4_sx/hunt/n3_all_30.jsonl.gz results/k4_sx/hunt/n3_all_40.jsonl.gz --every=50 > results/k4_sx/xcheck_hunt_n3.log 2>&1
python3 k4/sx_summary.py > /dev/null
echo all done
