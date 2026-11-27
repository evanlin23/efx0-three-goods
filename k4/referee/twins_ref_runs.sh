#!/bin/sh
# Referee runs for k4/referee/twins.md (log: results/k4_referee/twins_ref.log).
# Data: results/k4_twins/dbl_q3.json.gz, dbl_p4q4.json.gz from proof/k4-twins (git show ... > file)
cd "$(dirname "$0")"
Q=${Q3:-dbl_q3.json.gz}; P=${P4:-dbl_p4q4.json.gz}
python3 twins_ref.py $Q 80 1 > "${TMPDIR:-/tmp}"/tw1.out &
python3 twins_ref.py $P 60 2 dbl-P4-P4,dbl-P4-P4-c1,dbl-P4-Q4-c1 > "${TMPDIR:-/tmp}"/tw2.out &
python3 twins_ref.py $P 25 3 dbl-P4-Q4,dbl-Q4-Q4-c2 > "${TMPDIR:-/tmp}"/tw3.out &
wait
cat "${TMPDIR:-/tmp}"/tw1.out "${TMPDIR:-/tmp}"/tw2.out "${TMPDIR:-/tmp}"/tw3.out
python3 twins_ref.py $Q 20 9 all interior   # mutation (must fail)
