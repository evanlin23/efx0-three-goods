#!/bin/sh
# Referee runs for k4/referee/oc1max_multi.md §9 (Lemma M^c; log: results/k4_referee/mc_ref.log)
cd "$(dirname "$0")"
python3 mc_ref.py 15000 1 > "${TMPDIR:-/tmp}"/mc1.out &
python3 mc_ref.py 15000 2 > "${TMPDIR:-/tmp}"/mc2.out &
wait
cat "${TMPDIR:-/tmp}"/mc1.out "${TMPDIR:-/tmp}"/mc2.out
for mut in noFs noTauFs noComp; do python3 mc_ref.py 1500 3 $mut | head -2; done
