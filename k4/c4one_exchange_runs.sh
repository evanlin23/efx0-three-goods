#!/bin/bash
# Writes results/k4_c4one_exchange.log (k4/c4one.md §6): which single changed insertion step covers the runs that the
# theorems leave open (Lemmas X and X'), over the certified cores with one 4-good agent, n = 3..5.
# - "-i20 -E3": where the first working change lies and which agent it inserts (changes tried step by step from the
#   first, agents in index order);
# - "-i20 -Y -E4": the same, by the class of the uncovered run (k4/c4one.md §3), with omega of the new run;
# - "-i20 -Y -E4 -Z1" / "-Z3": only changes at the step that started q's block / only q inserted there.
# About 10 min on 4 CPUs (the -Y runs at n = 5 take the most).
cd "$(dirname "$0")/.."
F="results/k4_certs_3.json.gz results/k4_certs_4_n4_1.json.gz results/k4_certs_5_n4_1.json.gz"
L=results/k4_c4one_exchange.log; : > $L
for o in "-E3" "-Y -E4" "-Y -E4 -Z1" "-Y -E4 -Z3"; do
  python3 k4/c4one_exchange.py "-X -P2 -u2 -i20 -o0 -r1 -w0 -c0 -f3 $o" $F >> $L 2>&1
done
# From index order only (-i10): the step that started q's block changed; bit 1 of the category = the new agent is q.
python3 k4/c4one_exchange.py "-X -P2 -u2 -i10 -o0 -r1 -w0 -c0 -f3 -E" $F >> $L 2>&1
