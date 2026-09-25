#!/bin/bash
# Writes results/k4_c4one_tau.log (k4/c4one.md §6): for each insertion rule, the profiles (certified cores with one
# 4-good agent, n = 2..5) on which no allowed insertion sequence gives a run proved by the theorems (-P: those of
# k4/c4.md; -P2: also A4+ for every owner). About an hour on 4 CPUs. Modes (k4/c4check.c): -i2 every sequence until a
# success; -i0 index; -Q/-Q2 q first / as late as possible; -i6/-i10/-i11 index with one step changed; -i4/-i12/-i13/-i14
# least omega; -i15/-i17 least omega with tie-breaks; -i18/-i19 the exchange lemma of k4/c4one.md §6 from every sequence.
cd "$(dirname "$0")/.."
F="results/k4_certs_2.json.gz results/k4_certs_3.json.gz results/k4_certs_4_n4_1.json.gz results/k4_certs_5_n4_1.json.gz"
L=results/k4_c4one_tau.log; : > $L
for o in "-P -i2" "-P -Q -i2" "-P2 -i2" "-P2 -Q -i2" "-P2 -Q2 -i2" "-P2 -i0" "-P2 -Q -i0" "-P2 -Q2 -i0" \
         "-P2 -i6" "-P2 -i8" "-P2 -i10" "-P2 -i11" "-P2 -i4" "-P2 -i12" "-P2 -i13" "-P2 -i14" "-P -i14" \
         "-P2 -i15" "-P2 -i17" "-P -i17" "-P2 -i18" "-P2 -i19" "-P -i19"; do
  python3 k4/c4one_tau.py "-X $o -u2 -o0 -r1 -w0 -c0 -f3" $F >> $L 2>&1
done
