#!/bin/sh
# The independent GR checks (check_rules.py, MODE=GR) and the n = 4 rule census.  Run from the repository root.
D=results/k4_base_phantom/data
O=results/k4_base_phantom
MODE=GR python3 k4/base_phantom/check_rules.py $D/n5_5pure_s5o0_two_move_starts.jsonl.gz > $O/check_rules_GR_5pure.log
MODE=GR python3 k4/base_phantom/check_rules.py $D/two_move_starts_n5_partial6_s50.jsonl.gz > $O/check_rules_GR_n5partial.log
for f in onemove_hard_multi onemove_hard_hall2071 onemove_hard_pw291; do
  MODE=GR python3 k4/base_phantom/check_rules.py $D/$f.jsonl.gz > $O/check_rules_GR_$f.log
done
RULES=any,noP1,P1ok,E+noP1,E python3 k4/base_phantom/rules.py n4 $D/two_move_starts_n4.json.gz > $O/rules_n4.log
