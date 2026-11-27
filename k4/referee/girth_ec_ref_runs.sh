#!/bin/sh
# Referee runs for k4/referee/girth.md §6 (log: results/k4_referee/girth_ec_ref.log)
cd "$(dirname "$0")"
python3 girth_ec_ref.py 100000 1 > "${TMPDIR:-/tmp}"/ge1.out &
python3 girth_ec_ref.py 100000 2 > "${TMPDIR:-/tmp}"/ge2.out &
wait
cat "${TMPDIR:-/tmp}"/ge1.out "${TMPDIR:-/tmp}"/ge2.out
