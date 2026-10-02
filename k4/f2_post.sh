#!/bin/sh
# Steps 2 and 3 of k4/f2.md on the dumps of k4/f2_runs.sh: the lemma checks and coverage (k4/f2_lemmas.py), the second
# implementations (k4/f2_xcheck.py: dlrt4.c; k4/f2_xcheck2.py: c4x_check.py with its own (T3⁺) test), the f = 1 coverage
# on PR #75's T1-stuck dumps and the case-B scan. One worker; every step is bounded and skipped when its log is complete
# (it ends with "# no assertion failed" or "# done" or a "# " summary line, see done_log).
set -e
R=results/k4_f2
C=k4/suite/.cache
done_log() { [ -f "$1" ] && grep -q '^# \(no assertion failed\|done\|profiles\|[A-Z]\)' "$1"; }
# (a) coverage and the lemma checks at every T3-stage state of the dumps
done_log $R/coverage_n5fail.log || python3 k4/f2_lemmas.py $R/shapes_n5fail.jsonl.gz > $R/coverage_n5fail.log
done_log $R/coverage_rchunt.log || python3 k4/f2_lemmas.py $R/shapes_rchunt.jsonl.gz > $R/coverage_rchunt.log
for k in 0 1 2 3 4 5 6 7_28 7_29 7_30 7_31; do
  done_log $R/coverage_$k.log || python3 k4/f2_lemmas.py $R/shapes_$k.jsonl.gz > $R/coverage_$k.log
done
for k in 0 1 2 3 4 5 6 7; do
  done_log $R/coverage5_$k.log || python3 k4/f2_lemmas.py $R/shapes5_$k.jsonl.gz > $R/coverage5_$k.log
done
# (b) the same coverage (light: no Lemma 6+/8+/C checks) at the T3-stage states among PR #75's T1-stuck records, f >= 1
done_log $R/coverage_stuck.log || python3 k4/f2_lemmas.py --stuck --light results/k4_dl13_stuck/stuck_*.jsonl.gz \
  > $R/coverage_stuck.log
# (c) the lemma checks at every min-frozen state (Lemmas P, 6+, 8+, C) and every def > 0 state (the corollaries) of the
#     profiles of the n = 5 failures and of compute/k4-rc's hunt, and of random strict instances (not cores)
done_log $R/lemmas_profiles.log || python3 k4/f2_lemmas.py --profiles results/k4_rt4/n5b_failures_inst.json \
  results/k4_rt4/n5c_fail_inst.json $C/rc/hunt_fail10_sample_inst.json --all > $R/lemmas_profiles.log
done_log $R/lemmas_random.log || python3 k4/f2_lemmas.py --random 3000 --seed=7 --nmax=5 --mmax=12 > $R/lemmas_random.log
# (d) second implementations
done_log $R/xcheck2_n5fail_rchunt.log || python3 k4/f2_xcheck2.py $R/shapes_n5fail.jsonl.gz $R/shapes_rchunt.jsonl.gz \
  > $R/xcheck2_n5fail_rchunt.log
# (e) dlrt4.c (compute/k4-rt4's C tool) on every profile of the main data (k4/f2_runs.sh part (2), same source list) and
#     of the other inputs: its T3-stage states (f >= 2, no improving T1, T2, T4) and plain-T3 flags against the dumps
SRC="results/k4_gap/*.json.gz $C/pr75/results/k4_dl13_stuck/*.jsonl.gz results/k4_dl13/*.jsonl.gz results/k4_rt4/dump_[a-e]_*.jsonl.gz suite"
EX="--exclude-ids=rt4-n5m9-chain,rt4-n5m10-chain"
for k in 0 1 2 3; do
  done_log $R/xcheck_main_$k.log || python3 k4/f2_xcheck.py $SRC $EX --chunk=$k/4 "--dumps=$R/shapes_[0-7]*.jsonl.gz" \
    > $R/xcheck_main_$k.log
done
# (f) case B (a single frozen blocker with frozen needers only, its owner not the free end of a need path to it) at every
#     def > 0 state of the profiles with T3-stage states
done_log $R/caseb.log || python3 k4/f2_lemmas.py --caseb $R/shapes_[0-7]*.jsonl.gz $R/shapes_n5fail.jsonl.gz \
  $R/shapes_rchunt.jsonl.gz $R/shapes5_*.jsonl.gz > $R/caseb.log
done_log $R/xcheck_other.log || python3 k4/f2_xcheck.py results/k4_rt4/n5b_failures_inst.json results/k4_rt4/n5c_fail_inst.json \
  $C/rc/hunt_fail10_sample_inst.json "--dumps=$R/shapes_n5fail.jsonl.gz,$R/shapes_rchunt.jsonl.gz" > $R/xcheck_other.log
