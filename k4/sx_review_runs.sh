#!/bin/sh
# The runs added after the PR #80 review (k4/sx.md §4, §6), one process at a time, resumable (a complete log is
# skipped):
#   - the f >= 2 referee's classification of the maxima where neither Lemma A+ nor B+ applies (k4/sx_f2_classify.py);
#   - k4/sx_f2.py on the n5c profiles again (the current tool);
#   - k4/sx_zprime.py on the f = 1 keys of compute/k4-rc's profiles and of the T1-stuck profiles, and the hunt logs of
#     k4/sx_zprime_runs.sh (Lemma C' is now tested whenever tau2 is a leaf, not only when both terminals are leaves;
#     the logs made before that change were moved away first).
F=results/k4_sx/f2
done_() { [ -s $1 ] && grep -q '^# time' $1; }
done_ $F/classify_n5.log || python3 k4/sx_f2_classify.py $F/rt4_n5b_inst.json $F/rt4_n5c_inst.json > $F/classify_n5.log 2>&1
done_ $F/classify_catalogues.log || python3 k4/sx_f2_classify.py $(ls results/k4_sx/chunks/*@f2*.jsonl.gz) \
  results/k4_sx/chunks/gap_n4_1_c*.jsonl.gz > $F/classify_catalogues.log 2>&1
done_ $F/classify_t3stage.log || python3 k4/sx_f2_classify.py results/k4_sx/t3stage/keys.jsonl.gz > $F/classify_t3stage.log 2>&1
done_ $F/rt4_n5c.log || python3 k4/sx_f2.py --inst=$F/rt4_n5c_inst.json > $F/rt4_n5c.log 2>&1
done_ results/k4_sx/rc/zprime.log || python3 k4/sx_zprime.py results/k4_sx/rc/keys.jsonl.gz --examples=3 > results/k4_sx/rc/zprime.log 2>&1
T=results/k4_sx/t3stage
done_ $T/zprime_f1.log || python3 k4/sx_zprime.py $T/profiles_f1.jsonl.gz > $T/zprime_f1.log 2>&1
sh k4/sx_zprime_runs.sh
python3 k4/sx_summary.py > /dev/null
echo review runs done
