"""Coordinator's independent partial replay (2026-11-26) of the kgen-rounds session's ROUND+ counterexample
(branch proof/kgen-rounds, commit 202a4fd): n = 4, m = 7, every agent values every good (strictly positive), order
(2, 1, 3, 0).  Own code (oc1_mc2_rand.Inst: raw EFX0, official moves).  Checks: the number of EFX0 allocations and of
those dominating the picks; no free completion at the picks, after any single move, or after any two vertex-disjoint
moves applied together (a round of two chains; with n = 4 this covers every round with at most two moves)."""
import itertools
import _paths  # noqa: F401
from oc1_mc2_rand import Inst

vals = [[304, 35, 1, 2864, 610, 2535, 950], [432, 643, 29, 1067, 71, 2469, 764],
        [90, 582, 165, 1265, 981, 2483, 1970], [434, 642, 29, 1068, 69, 2467, 764]]
I = Inst([list(range(7))] * 4, vals)
p = I.sd([2, 1, 3, 0]); base = [[g] for g in p]
print('picks', p)
cnt = dom = 0
for asg in itertools.product(range(4), repeat=7):
    B = [[g for g in range(7) if asg[g] == i] for i in range(4)]
    if I.efx0(B):
        cnt += 1; dom += all(I.V(i, B[i]) >= I.v[i][p[i]] for i in range(4))
print('EFX0 allocations', cnt, '| dominating the picks', dom)


def free(b):
    J = [g for g in range(I.m) if all(g not in x for x in b)]
    for a in itertools.product(range(I.n), repeat=len(J)):
        B = [list(x) for x in b]
        for g, y in zip(J, a): B[y].append(g)
        if I.efx0(B): return True
    return False


M = list(I.moves(base))
print('free completion at the picks', free(base), '| single moves', len(M), '| with a free completion',
      sum(free([list(b) for b in s]) for s in M))
ch = [(s, {i for i in range(4) if sorted(s[i]) != sorted(base[i])}) for s in M]
tried = good = 0
for (s1, A1), (s2, A2) in itertools.combinations(ch, 2):
    if A1 & A2: continue
    nb = [list(s1[i]) if i in A1 else (list(s2[i]) if i in A2 else list(base[i])) for i in range(4)]
    allg = [g for b in nb for g in b]
    if len(allg) != len(set(allg)): continue
    tried += 1; good += free(nb)
print('rounds of two disjoint moves', tried, '| with a free completion', good)
