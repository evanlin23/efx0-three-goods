#!/bin/sh
# The OC2 data of k4/oc1max_multi.md §8 (run from the repository root; about an hour on 4 CPUs).
R=results/k4_oc1max_multi
python3 k4/oc1max_multi/cex_check.py > $R/cex_check.log
# OUT=$R/oc1_fail_walk.jsonl python3 k4/oc1max_multi/walk_fail.py 2000 7 > $R/walk_fail.log; gzip $R/oc1_fail_walk.jsonl
W=$R/oc1_fail_walk.jsonl.gz
python3 k4/oc1max_multi/lift.py $W > $R/lift.log
python3 k4/oc1max_multi/lift_shape.py $W > $R/lift_shape.log
python3 k4/oc1max_multi/reduce_check.py $W > $R/reduce_check.log
python3 k4/oc1max_multi/reduce_mech.py $W > $R/reduce_mech.log
python3 k4/oc1max_multi/sharing.py $R/hard2_starts.jsonl.gz $R/hard2_starts_n5.jsonl.gz > $R/sharing.log
