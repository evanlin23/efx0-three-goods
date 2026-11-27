#!/bin/sh
# Referee runs for k4/referee/oc1max_multi.md (log: results/k4_referee/multi_ref.log); 4 processes in parallel
cd "$(dirname "$0")"
python3 multi_ref.py 300000 3 4 1 > "${TMPDIR:-/tmp}"/mr1.out &
python3 multi_ref.py 150000 4 5 2 > "${TMPDIR:-/tmp}"/mr2.out &
python3 multi_ref.py 150000 5 5 3 > "${TMPDIR:-/tmp}"/mr3.out &
python3 multi_ref.py 200000 3 5 4 > "${TMPDIR:-/tmp}"/mr4.out &
wait
cat "${TMPDIR:-/tmp}"/mr1.out "${TMPDIR:-/tmp}"/mr2.out "${TMPDIR:-/tmp}"/mr3.out "${TMPDIR:-/tmp}"/mr4.out
for mut in noDEMAND noCROWD noHEAD noK2 noK3 noW1; do python3 multi_ref.py 40000 3 4 5 $mut; done
python3 ring_ref.py 100000 3 5 7   # log: results/k4_referee/ring_ref.log
