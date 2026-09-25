#!/bin/bash
# The sub-searches of LB4r in k4/c4.md §6.2: every strict profile, every insertion sequence (-i1).
# Writes results/k4_c4_variants.log (append). Needs the split core lists written by k4/c4_split_cores.py.
cd "$(dirname "$0")/.."
L=results/k4_c4_variants.log
S=results/k4_c4_split
python3 k4/c4_split_cores.py
run() { echo "## $*" >> $L; python3 k4/lb4_run.py "$@" --show=3 >> $L 2>&1; }
run $S/k4_certs_2_n4eq1.json.gz $S/k4_certs_3_n4eq1.json.gz results/k4_certs_4_n4_1.json.gz -i1 -u2 -o0 -r1 -w0 -c0
run $S/k4_certs_3_n4eq1.json.gz results/k4_certs_4_n4_1.json.gz -i1 -u2 -o2 -r1 -w0 -c0
run $S/k4_certs_2_n4eq2.json.gz $S/k4_certs_3_n4eq2.json.gz -i1 -u3 -o0 -r1 -w1 -c1
run $S/k4_certs_2_n4eq2.json.gz $S/k4_certs_3_n4eq2.json.gz -i1 -u2 -o0 -r2 -w1 -c1
run results/k4_certs_2.json.gz results/k4_certs_3.json.gz -i1 -u0 -o0 -r1 -w1 -c1
run results/k4_certs_2.json.gz results/k4_certs_3.json.gz results/k4_certs_4_n4_1.json.gz results/k4_certs_4_n4_2.json.gz results/k4_certs_4_n4_3.json.gz -i1 -u0 -o0 -r2 -w1 -c1
run results/k4_certs_2.json.gz results/k4_certs_3.json.gz results/k4_certs_4_n4_1.json.gz results/k4_certs_4_n4_2.json.gz results/k4_certs_4_n4_3.json.gz -i1 -u0 -o2 -r3 -w1 -c1
run $S/k4_certs_2_n4eq2.json.gz $S/k4_certs_3_n4eq2.json.gz -i1 -u2 -o0 -r2 -w0 -c0
