#!/bin/sh
# Referee runs for k4/referee/oc1_hall_d1.md (log: results/k4_referee/hall21_ref.log)
cd "$(dirname "$0")"
python3 hall21_ref.py cex
python3 hall21_ref.py 400000 3 4 1 > "${TMPDIR:-/tmp}"/h1.out &
python3 hall21_ref.py 200000 4 5 2 > "${TMPDIR:-/tmp}"/h2.out &
python3 hall21_ref.py 150000 5 5 3 > "${TMPDIR:-/tmp}"/h3.out &
python3 hall21_ref.py 300000 2 3 4 > "${TMPDIR:-/tmp}"/h4.out &
wait
cat "${TMPDIR:-/tmp}"/h1.out "${TMPDIR:-/tmp}"/h2.out "${TMPDIR:-/tmp}"/h3.out "${TMPDIR:-/tmp}"/h4.out
