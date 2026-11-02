#!/bin/bash
# Regenerates every log of k4/de4.md §4 into results/k4_de4/ (about 1.5 h on 4 CPUs, without exhaustive_3).
# The C exhaustive runs are separate (exhaustive_3.log about 1 h; exhaustive_4_n4_1.log a few minutes):
#   python3 k4/de4/run_exhaustive.py k4_certs_3.json.gz; python3 k4/de4/run_exhaustive.py k4_certs_4_n4_1.json.gz
set -u
cd "$(dirname "$0")/../.."
L=results/k4_de4
run() { local log=$1; shift; { echo "\$ $*"; "$@"; } > "$L/$log" 2>&1; echo "done $log: $(tail -1 $L/$log)"; }
run xcheck.log            python3 k4/de4/check.py xcheck
run variants.log          python3 k4/de4/variants.py
run suite.log             python3 k4/de4/check.py suite
run exhaustive_2.log      python3 k4/de4/check.py exhaustive k4_certs_2.json.gz 2
run exhaustive_2_c.log    python3 k4/de4/run_exhaustive.py k4_certs_2.json.gz
run certs_3.log           python3 k4/de4/check.py certs k4_certs_3.json.gz 300
run certs_4.log           python3 k4/de4/check.py certs k4_certs_4_n4_1.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz,k4_certs_4_pure.json.gz 40
run certs_5_pure.log      python3 k4/de4/check.py certs k4_certs_5_pure.json.gz 2
run certs_5_n4_34.log     python3 k4/de4/check.py certs k4_certs_5_n4_3.json.gz,k4_certs_5_n4_4.json.gz 1
run r1ties.log            python3 k4/de4/check.py r1ties 100
run moves.log             python3 k4/de4/check.py moves
run algo_suite.log        python3 k4/de4/check.py algo
run algo_random.log       python3 k4/de4/check.py algo k4_certs_3.json.gz,k4_certs_4_n4_1.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz,k4_certs_4_pure.json.gz 20
run verify_lemmas.log     python3 k4/de4/verify_lemmas.py 3
echo ALLDONE
