#!/bin/sh
# Referee runs for k4/referee/oc1max_multi.md §8 (Theorem U; log: results/k4_referee/theorem_u_ref.log)
cd "$(dirname "$0")"
python3 theorem_u_ref.py 200000 3 5 1 > "${TMPDIR:-/tmp}"/tu1.out &
python3 theorem_u_ref.py 100000 4 5 2 > "${TMPDIR:-/tmp}"/tu2.out &
wait
python3 theorem_u_ref.py 60000 3 5 3 anychain > "${TMPDIR:-/tmp}"/tu3.out &
python3 theorem_u_ref.py 60000 3 5 4 noEJ > "${TMPDIR:-/tmp}"/tu4.out &
wait
cat "${TMPDIR:-/tmp}"/tu1.out "${TMPDIR:-/tmp}"/tu2.out "${TMPDIR:-/tmp}"/tu3.out "${TMPDIR:-/tmp}"/tu4.out
