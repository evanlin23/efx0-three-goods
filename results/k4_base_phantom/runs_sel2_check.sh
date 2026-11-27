#!/bin/sh
# Second implementation of GR on the certifier's complete sel2 lists (583,680 starts), in 10 chunks (about 4 h).
D=results/k4_base_phantom/data
O=results/k4_base_phantom
for i in 0 1 2 3 4 5 6 7 8 9; do
  MODE=GR python3 k4/base_phantom/check_rules.py $D/two_move_starts_n5_sel2.json.gz 10 $i > $O/check_rules_GR_n5sel2_part$i.log
done
