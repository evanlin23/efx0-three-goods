"""Lemma EX (proof/k4-matching, k4/matching.md §3) is sufficient but not necessary (k4/oc1_hall.md §23.1).
lb4-n2m5-upgrade (n = 2), order (0, 1), chain (0, 1), H_0 = {2, 3}, owner k = 0: B' has an S* completion owned by k
(the crowded head takes junk good 1), but no H inside J' meets EX's hypotheses ((1') for the head at its B' value, and
a matching on N = {} with at least |H| - s edges, s = 1).

    python3 k4/oc1_hall/ex_not_exact.py
"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, bundles_of, frozen_set, threatened, efx0
from greedy_rules import apply_chain
sets, vals = [[0, 2, 3, 4], [1, 2, 3, 4]], [[1, 4, 6, 8], [2, 4, 5, 8]]
I = Inst(sets, vals, 5); Y = picks(I, (0, 1)); P = Picks(I, Y); base = base_of_picks(I, Y)
b2 = apply_chain(I, P, base, (0, 1), (2, 3)); B2 = bundles_of(I, b2); J2 = [g for g in range(5) if b2[g] < 0]
F2 = frozen_set(I, b2); s = sum(1 for j in [1] if j not in F2 and len(B2[j]) == 1)
print('picks', Y, "B'", B2, "J'", J2, 'frozen after', F2, 's =', s, '(N is empty: no agent off the chain)')
ok_any = False
for r in range(len(J2) + 1):
    for H in itertools.combinations(J2, r):
        X = B2[0] + [g for g in J2 if g not in H]
        c1 = not threatened(I, 1, I.val(1, B2[1]), X)
        c2 = 0 >= len(H) - s
        print("  H =", H, "X =", X, "(1') for the head:", c1, "; matching with >= |H| - s edges:", c2)
        ok_any |= c1 and c2
print("EX's hypothesis holds for some H:", ok_any)
X = [[2, 3, 0], [4, 1]]
print('S* completion owned by k (head compensated by junk 1):', X, 'EFX0 (raw):', efx0(I, X))
