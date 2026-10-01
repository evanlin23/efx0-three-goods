#!/bin/sh
# The key-graph runs of k4/sx.md (workstream proof/k4-sx), one process at a time.
# #53's catalogues at 245040b (k4/strategy.md §4):
#   mkdir -p k4/suite/.cache/gapbench && git archive 245040b results/k4_gap | tar -x -C k4/suite/.cache/gapbench
set -e
C=k4/suite/.cache/gapbench/results/k4_gap
O=results/k4_sx
mkdir -p $O
run() {   # name, args...
  name=$1; shift
  [ -s $O/keys_$name.log ] && grep -q '^# time' $O/keys_$name.log && return 0
  python3 k4/sx_keygraph.py "$@" --dump=$O/keys_$name.jsonl.gz > $O/keys_$name.log 2>&1
}
run gap_n4_1 catalog $C/gap_n4_1.json.gz
run hunt_n4_2_all catalog $C/hunt_n4_2_all.json.gz
run gap_n4_2_s4000 catalog $C/gap_n4_2_s4000.json.gz
run gap_n4_3_s4000 catalog $C/gap_n4_3_s4000.json.gz
run hunt_n4_3_s400k catalog $C/hunt_n4_3_s400k.json.gz
run gap_n4_pure_s4000 catalog $C/gap_n4_pure_s4000.json.gz
run hunt_n4_pure_s400k catalog $C/hunt_n4_pure_s400k.json.gz
run hard_hunt catalog $C/hard_hunt.json.gz
run suite suite
run gap_n3 catalog $C/gap_n3.json.gz
