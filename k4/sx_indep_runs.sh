#!/bin/sh
# The PR #80 referee's independent checker k4/sx_indep.py (no repository code) on the non-completable f = 1 keys of
# k4/sx.md §4: the n = 4 hunts, compute/k4-rc's 45 profiles and the first 800 profiles of four n = 3 hunt files.
# One process at a time, resumable (a complete log is skipped). Logs: results/k4_sx/indep_*.log.
O=results/k4_sx
run() {  # name source [max]
  [ -s $O/indep_$1.log ] && grep -q '^# time' $O/indep_$1.log && return 0
  python3 k4/sx_indep.py $2 $3 > $O/indep_$1.log 2>&1
}
run rc results/k4_sx/rc/rc_fail_inst.json
run n4_3_r40k results/k4_sx/hunt/n4_3_r40k.jsonl.gz
run n4_pure_r40k results/k4_sx/hunt/n4_pure_r40k.jsonl.gz
for f in n3_all_10 n3_all_20 n3_all_30 n3_all_40; do run ${f}_800 results/k4_sx/hunt/$f.jsonl.gz 800; done
run n4_pure_r400k results/k4_sx/hunt/n4_pure_r400k.jsonl.gz
