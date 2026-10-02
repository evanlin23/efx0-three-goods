#!/bin/sh
# Step 1 of k4/f2.md: every f >= 2 T3-stage state of the available data, with its improving (T3) and (T3⁺) moves, in
# slices of the deduplicated profile list (one worker; each slice runs a few minutes). Resumable: a slice whose log is
# complete (it ends with "# done", or, for the first slices, has its "profiles" count line) is skipped; a cut slice is
# rerun from its start.
# Inputs: main's results/ (since #75 and #86 also PR #75's results/k4_dl13_stuck/ and compute/k4-rt4's n = 5 dumps)
# and compute/k4-rc's hunt (branch origin/compute/k4-rc), copied once:
#   mkdir -p k4/suite/.cache/pr75/results k4/suite/.cache/rc && cp -r results/k4_dl13_stuck k4/suite/.cache/pr75/results/
#   git show origin/compute/k4-rc:results/k4_rc/hunt_fail10_sample_inst.json > k4/suite/.cache/rc/hunt_fail10_sample_inst.json
# (part (2) reads PR #75's dumps from the cache path, as when slices 0-6 ran, so that the deduplicated list is unchanged).
# Slices 0-6 of part (2) were run before the key-graph test was widened to its definition (an edge from any state of
# the key to any state of a key with a smaller def*); they test the narrower form (an edge to a state of smaller
# deficit than the source state), which implies it.
set -e
C=k4/suite/.cache
done_log() { [ -f "$1" ] && { grep -q '^# done' "$1" || grep -q '^profiles ' "$1"; }; }
# (1) the 10 failing n = 5 profiles of DL_RT4 (K4.DL2.RT4)
done_log results/k4_f2/shapes_n5fail.log || python3 k4/f2_shapes.py results/k4_rt4/n5b_failures_inst.json \
  results/k4_rt4/n5c_fail_inst.json --out=results/k4_f2/shapes_n5fail.jsonl.gz > results/k4_f2/shapes_n5fail.log
# (2) main's data before #86 and PR #75's dumps: 7 eighths, then the last eighth in four parts (the heavy n = 5 hunt
#     states). The source list is frozen as it was when slices 0-6 ran (79,372 distinct profiles): the dumps of
#     results/k4_rt4/ merged by #86 (dump_n4_3_x*, dump_n5*) and the suite's two later instances are left out here (the
#     n = 5 dumps are part (4); the two instances are failing profiles of part (1)).
SRC="results/k4_gap/*.json.gz $C/pr75/results/k4_dl13_stuck/*.jsonl.gz results/k4_dl13/*.jsonl.gz results/k4_rt4/dump_[a-e]_*.jsonl.gz suite"
EX="--exclude-ids=rt4-n5m9-chain,rt4-n5m10-chain"
for k in 0 1 2 3 4 5 6; do
  done_log results/k4_f2/shapes_$k.log && continue
  python3 k4/f2_shapes.py $SRC $EX --chunk=$k/8 --out=results/k4_f2/shapes_$k.jsonl.gz > results/k4_f2/shapes_$k.log
done
for k in 28 29 30 31; do
  done_log results/k4_f2/shapes_7_$k.log && continue
  python3 k4/f2_shapes.py $SRC $EX --chunk=$k/32 --out=results/k4_f2/shapes_7_$k.jsonl.gz > results/k4_f2/shapes_7_$k.log
done
# (3) compute/k4-rc's hunt from the failing profiles (54 profiles with DL_RT4 failures at f = 2 and f = 3)
done_log results/k4_f2/shapes_rchunt.log || python3 k4/f2_shapes.py $C/rc/hunt_fail10_sample_inst.json \
  --out=results/k4_f2/shapes_rchunt.jsonl.gz > results/k4_f2/shapes_rchunt.log
# (4) compute/k4-rt4's n = 5 dumps (#86: n5b random n4_3/n4_4 runs, n5c pure and big-top runs): the 1,902 profiles with
#     a dumped f >= 2 state whose branches name no improving (T1), (T2), (T4) move (--t3br), 8 slices
SRC5="results/k4_rt4/dump_n5b_3.jsonl.gz results/k4_rt4/dump_n5b_3bt.jsonl.gz results/k4_rt4/dump_n5b_4.jsonl.gz results/k4_rt4/dump_n5b_4bt.jsonl.gz results/k4_rt4/dump_n5c_purebt.jsonl.gz results/k4_rt4/dump_n5c_pure.jsonl.gz"
for k in 0 1 2 3 4 5 6 7; do
  done_log results/k4_f2/shapes5_$k.log && continue
  python3 k4/f2_shapes.py $SRC5 --t3br --chunk=$k/8 --out=results/k4_f2/shapes5_$k.jsonl.gz > results/k4_f2/shapes5_$k.log
done
