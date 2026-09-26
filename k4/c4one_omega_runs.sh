#!/bin/bash
# Writes the logs of k4/c4one.md §6 on Lemma Ω and on runs with P-steps in any order (about 70 min on 4 CPUs):
# - results/k4_c4one_omega1.log: Lemma Ω on the uncovered (Tc) runs with x = q, then on every uncovered run with any x
#   (the runs lb4.c makes, LB's P-step key);
# - results/k4_c4one_general.log: Lemmas X' and X over runs of Phase 1 with P-steps in any order (k4/c4check.c -G);
# - results/k4_c4one_omega1_general.log: Lemma Ω on every uncovered run of that kind, any x.
cd "$(dirname "$0")/.."
F="results/k4_certs_3.json.gz results/k4_certs_4_n4_1.json.gz results/k4_certs_5_n4_1.json.gz"
{ time python3 k4/c4tools/c4omega1.py $F; } > results/k4_c4one_omega1.log 2>&1
{ time python3 k4/c4tools/c4omega1.py $F --any; } >> results/k4_c4one_omega1.log 2>&1
L=results/k4_c4one_general.log
echo "# Lemmas X' (-i20) and X (-i19) over runs of Phase 1 with P-steps in any order (k4/c4check.c -G)" > $L
for o in "-i20" "-i19"; do
  { time python3 k4/c4one_tau.py "-X -P2 -u2 $o -o0 -r1 -w0 -c0 -f3 -G" $F; } >> $L 2>&1
done
{ time python3 k4/c4tools/c4omega1.py $F --any --general; } > results/k4_c4one_omega1_general.log 2>&1
