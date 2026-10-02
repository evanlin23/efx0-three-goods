#!/bin/sh
# Case (i) of K4.SX.COVER (k4/thetab.md §7): k4/thetab_cover.py on PR #80's dumps of non-completable f = 1 keys
# (results/k4_sx/, with PR #80's k4/sx_keygraph.py and k4/sx_zprime.py, all on main).
# One worker, sequential. Logs in results/k4_thetab/. A run whose log exists is skipped (delete it to redo).
set -e
R=results/k4_thetab
H=results/k4_sx
mkdir -p $R
run() { out=$R/$1.log; shift; [ -s $out ] && return 0; python3 "$@" > $out.tmp && mv $out.tmp $out; }
run cover_n4_hunts k4/thetab_cover.py $H/hunt/n4_3_r40k.jsonl.gz $H/hunt/n4_pure_r40k.jsonl.gz
run cover_n4_pure_r400k k4/thetab_cover.py $H/hunt/n4_pure_r400k.jsonl.gz
run cover_n5 k4/thetab_cover.py $H/hunt/n5_pure_r1000_3000.jsonl.gz $H/hunt/n5_pure_r1000_4000.jsonl.gz
run cover_rc k4/thetab_cover.py $H/rc/keys.jsonl.gz
run cover_t3stage k4/thetab_cover.py $H/t3stage/profiles_f1.jsonl.gz
for s in 10 20 30 40; do
  run cover_n3_all_${s}_e5 k4/thetab_cover.py $H/hunt/n3_all_$s.jsonl.gz --every=5
done
# Conjecture S1c (k4/thetab.md §7.1): every Z′-maximum of every non-completable f = 1 key of PR #80's dumps
run xbt_n3_all k4/thetab_xbt.py $H/hunt/n3_all_0.jsonl.gz $H/hunt/n3_all_10.jsonl.gz $H/hunt/n3_all_20.jsonl.gz \
  $H/hunt/n3_all_30.jsonl.gz $H/hunt/n3_all_40.jsonl.gz $H/hunt/n3_all_50.jsonl.gz
run xbt_n4 k4/thetab_xbt.py $H/hunt/n4_2_r20k.jsonl.gz $H/hunt/n4_3_r40k.jsonl.gz $H/hunt/n4_pure_r40k.jsonl.gz \
  $H/hunt/n4_pure_r400k.jsonl.gz
run xbt_n5_rc_t3stage k4/thetab_xbt.py $H/hunt/n5_*.jsonl.gz $H/rc/keys.jsonl.gz $H/t3stage/profiles_f1.jsonl.gz
