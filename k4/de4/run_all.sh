#!/bin/bash
# Regenerates every log of k4/de4.md §4 and §7.8 into results/k4_de4/ (about 4 h on 4 CPUs, without exhaustive_3).
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
run dead_stuck_n4.log     python3 k4/de4/dead.py stuck k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz 4000 40 1000
run dead_stuck_rand.log   python3 k4/de4/dead.py stuck rand 2500 40 2000
run dead_stuck_n5.log     python3 k4/de4/dead.py stuck k4_certs_5_n4_3.json.gz,k4_certs_5_n4_4.json.gz 60 40 5000
run dead_stuck_stuckhyper.log python3 k4/de4/dead.py stuck hypergraphs:results/k4_de4/stuck_hypergraphs.json 1000 40 7000
run dead_hard_v9.log      python3 k4/de4/dead.py dead 'fixed:[[0,2,5,6],[0,3,4,6],[1,2,4,6],[1,3,5]]' 500 40 3000
run dead_hard_n4.log      python3 k4/de4/dead.py dead k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz 1000 40 4000
run dead_hard_stuckhyper.log python3 k4/de4/dead.py dead hypergraphs:results/k4_de4/stuck_hypergraphs.json 1000 40 6000
run dead_minimal_v9.log   python3 k4/de4/dead.py minimal 'fixed:[[0,2,5,6],[0,3,4,6],[1,2,4,6],[1,3,5]]' 500 40 3000
run dead_minimal_stuckhyper.log python3 k4/de4/dead.py minimal hypergraphs:results/k4_de4/stuck_hypergraphs.json 1000 40 6000
run lemma15_suite.log     python3 k4/de4/lemma15.py suite
run lemma15_v9.log        python3 k4/de4/lemma15.py 'fixed:[[0,2,5,6],[0,3,4,6],[1,2,4,6],[1,3,5]]' 500 40 8000
run lemma15_n4.log        python3 k4/de4/lemma15.py k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz 200 40 9000
run lemma15_rand.log      python3 k4/de4/lemma15.py rand 500 40 10000
echo ALLDONE
