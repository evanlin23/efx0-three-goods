#!/bin/sh
# Referee runs for k4/referee/d1.md (log: results/k4_referee/d1_ref.log)
cd "$(dirname "$0")"
python3 d1_ref.py p3
python3 d1_ref.py tied
python3 d1_ref.py p1 300000 3 4 1 > "${TMPDIR:-/tmp}"/d1a.out &
python3 d1_ref.py p1w 100000 3 5 2 > "${TMPDIR:-/tmp}"/d1b.out &
python3 d1_ref.py p2w 200000 3 strict > "${TMPDIR:-/tmp}"/d1c.out &
python3 d1_ref.py p2w 200000 4 ties > "${TMPDIR:-/tmp}"/d1d.out &
wait
python3 d1_ref.py p1 120000 4 5 5 > "${TMPDIR:-/tmp}"/d1e.out
cat "${TMPDIR:-/tmp}"/d1a.out "${TMPDIR:-/tmp}"/d1b.out "${TMPDIR:-/tmp}"/d1c.out "${TMPDIR:-/tmp}"/d1d.out "${TMPDIR:-/tmp}"/d1e.out
