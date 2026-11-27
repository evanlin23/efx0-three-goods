#!/bin/sh
# Reproduce every log of this workstream (about 30 min on 4 CPUs).  Run from the repository root.
set -e
D=results/k4_base_phantom/data
O=results/k4_base_phantom
ONE=$D/onemove_hard_multi.jsonl.gz,$D/onemove_hard_hall2071.jsonl.gz,$D/onemove_hard_pw291.jsonl.gz
python3 k4/base_phantom/base_census.py > $O/base_census.log
python3 k4/base_phantom/classes.py > $O/classes.log
python3 k4/base_phantom/ring2.py > $O/ring2.log
python3 k4/base_phantom/deadends.py onemove $ONE > $O/deadends_onemove.log
python3 k4/base_phantom/deadends.py 5pure $D/n5_5pure_s5o0_two_move_starts.jsonl.gz > $O/deadends_5pure.log
python3 k4/base_phantom/deadends.py walk $D/multi_oc1_fail_walk.jsonl.gz > $O/deadends_walk.log
python3 k4/base_phantom/deadends.py n5partial $D/two_move_starts_n5_partial6_s50.jsonl.gz > $O/deadends_n5partial.log
python3 k4/base_phantom/deadends.py n4 $D/two_move_starts_n4.json.gz > $O/deadends_n4.log
for n in onemove 5pure walk n5partial n4; do
  python3 k4/base_phantom/check_deadends.py $O/deadends_$n.jsonl.gz > $O/check_deadends_$n.log
done
export RULES=any,noP1,P1ok,E+noP1,E
python3 k4/base_phantom/rules.py onemove $ONE > $O/rules_onemove.log
python3 k4/base_phantom/rules.py 5pure $D/n5_5pure_s5o0_two_move_starts.jsonl.gz > $O/rules_5pure.log
python3 k4/base_phantom/rules.py walk $D/multi_oc1_fail_walk.jsonl.gz > $O/rules_walk.log
python3 k4/base_phantom/rules.py n5partial $D/two_move_starts_n5_partial6_s50.jsonl.gz > $O/rules_n5partial.log
python3 k4/base_phantom/rules.py n4 $D/two_move_starts_n4.json.gz > $O/rules_n4.log
