#!/bin/sh
# Second implementation of GR on the certifier's complete sel2 lists (583,680 starts), in 10 chunks (about 3 h).
# Each chunk writes to a temporary file and is moved into results/ only when it is complete.
# Usage: sh results/k4_base_phantom/runs_sel2_check.sh [FIRST_CHUNK]
D=results/k4_base_phantom/data
O=results/k4_base_phantom
TMP=${TMPDIR:-/tmp}
for i in 0 1 2 3 4 5 6 7 8 9; do
  [ "$i" -lt "${1:-0}" ] && continue
  MODE=GR python3 k4/base_phantom/check_rules.py $D/two_move_starts_n5_sel2.json.gz 10 $i > $TMP/sel2_part$i.log && \
    mv $TMP/sel2_part$i.log $O/check_rules_GR_n5sel2_part$i.log
done
