#!/bin/sh
# Referee runs for k4/referee/lift.md (log: results/k4_referee/lift_ref.log).
# CEX = results/k4_oc1max/oc1max_cex_n4.json from compute/k4-oc1max-cert (git show ... > cex.json)
cd "$(dirname "$0")"
X=${CEX:-cex.json}
python3 lift_ref.py 25000 1 none $X > "${TMPDIR:-/tmp}"/lf1.out &
python3 lift_ref.py 25000 2 none $X > "${TMPDIR:-/tmp}"/lf2.out &
python3 lift_ref.py 25000 3 junkmid $X > "${TMPDIR:-/tmp}"/lf3.out &
python3 lift_ref.py 25000 4 nofav $X > "${TMPDIR:-/tmp}"/lf4.out &
wait
cat "${TMPDIR:-/tmp}"/lf1.out "${TMPDIR:-/tmp}"/lf2.out "${TMPDIR:-/tmp}"/lf3.out "${TMPDIR:-/tmp}"/lf4.out
