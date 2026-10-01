#!/bin/sh
# Step 1 of k4/f2.md: every f >= 2 T3-stage state of the available data, with its improving (T3) and (T3⁺) moves, in
# slices of the deduplicated profile list (one worker; each slice runs a few minutes). Resumable: a slice whose log is
# complete (it ends with "# done", or, for the first slices, has its "profiles" count line) is skipped; a cut slice is
# rerun from its start.
# Inputs besides main's results/: PR #75's dumps (results/k4_dl13_stuck/ on origin/proof/k4-dl13) and the n = 5 runs of
# compute/k4-rt4 that refute DL_RT4 (origin/compute/k4-rt4-n5b, origin/compute/k4-rt4-n5c):
#   mkdir -p k4/suite/.cache/pr75 k4/suite/.cache/rt4n5
#   git archive -o /tmp/stuck.tar origin/proof/k4-dl13 results/k4_dl13_stuck && tar -xf /tmp/stuck.tar -C k4/suite/.cache/pr75
#   git archive -o /tmp/n5b.tar origin/compute/k4-rt4-n5b results/k4_rt4/dump_n5b_3.jsonl.gz results/k4_rt4/dump_n5b_3bt.jsonl.gz \
#     results/k4_rt4/dump_n5b_4.jsonl.gz && tar -xf /tmp/n5b.tar -C k4/suite/.cache/rt4n5
#   git archive -o /tmp/n5c.tar origin/compute/k4-rt4-n5c results/k4_rt4/dump_n5c_purebt.jsonl.gz results/k4_rt4/dump_n5c_pure.jsonl.gz \
#     results/k4_rt4/n5c_fail_inst.json && tar -xf /tmp/n5c.tar -C k4/suite/.cache/rt4n5
#   k4/suite/.cache/rt4n5/n5b_inst.json, n5c_inst.json: the 10 failing profiles (2 + 8) as instance lists
#     (n5b_failures_inst.json of the n5b branch; n5c_fail_inst.json of the n5c branch)
set -e
C=k4/suite/.cache
done_log() { [ -f "$1" ] && { grep -q '^# done' "$1" || grep -q '^profiles ' "$1"; }; }
# (1) the failing n = 5 profiles of DL_RT4
done_log results/k4_f2/shapes_n5fail.log || python3 k4/f2_shapes.py $C/rt4n5/n5b_inst.json $C/rt4n5/n5c_inst.json \
  --out=results/k4_f2/shapes_n5fail.jsonl.gz > results/k4_f2/shapes_n5fail.log
# (2) main's data and PR #75's dumps, 8 slices
SRC="results/k4_gap/*.json.gz $C/pr75/results/k4_dl13_stuck/*.jsonl.gz results/k4_dl13/*.jsonl.gz results/k4_rt4/*.jsonl.gz suite"
for k in 0 1 2 3 4 5 6 7; do
  done_log results/k4_f2/shapes_$k.log && continue
  python3 k4/f2_shapes.py $SRC --chunk=$k/8 --out=results/k4_f2/shapes_$k.jsonl.gz > results/k4_f2/shapes_$k.log
done
# (3) the f >= 2 profiles of the n = 5 dumps of compute/k4-rt4 (n5b, n5c), 8 slices
SRC5="$C/rt4n5/results/k4_rt4/dump_n5b_3.jsonl.gz $C/rt4n5/results/k4_rt4/dump_n5b_3bt.jsonl.gz $C/rt4n5/results/k4_rt4/dump_n5b_4.jsonl.gz $C/rt4n5/results/k4_rt4/dump_n5c_purebt.jsonl.gz $C/rt4n5/results/k4_rt4/dump_n5c_pure.jsonl.gz"
for k in 0 1 2 3 4 5 6 7; do
  done_log results/k4_f2/shapes5_$k.log && continue
  python3 k4/f2_shapes.py $SRC5 --chunk=$k/8 --out=results/k4_f2/shapes5_$k.jsonl.gz > results/k4_f2/shapes5_$k.log
done
