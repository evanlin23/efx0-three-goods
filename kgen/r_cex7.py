"""The n = 7 counterexample to the release bound (R) (kgen/n3.md §15.16; found by k3-oc1,
attempts/k4-k3oc1-release-bound.md on claude/k4-k3-oc1; checked here).  A ledger-core draft with one terminal where
every Rule E rotation from E_t leaves omega' = 2 after LB's upgrades, yet completes with owner k.
Per rotation: omega' (after upgrades); lb2; this note's Lemma 1 test with owner none or k (kgen/k3max_owner.py); and
an exhaustive search over every completion keeping the bases (raw EFX0, values 4, 3, 2).
Needs K3OC1 as kgen/k3max_t1.py.

    K3OC1=... python3 kgen/r_cex7.py"""
import sys, os, itertools
K = os.environ.get('K3OC1', os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'k4', 'k3oc1'))
sys.path.insert(0, K); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k3lib import base_of
from lbtest import lb2, parts, exposed, upgrade
from thm_bstar import chains_to
from k3max_t1 import rotate
from k3max_ruleE import topo, rule_e_chain
from k3max_owner import own_none_or_k

rk = [(0, 5, 7), (3, 2, 8), (2, 6, 9), (3, 10, 6), (4, 11, 5), (0, 1, 5), (6, 4, 1)]; m = 12; n = 7
order = (0, 3, 1, 2, 4, 6, 5)
val = {(i, g): x for i in range(n) for g, x in zip(rk[i], (4, 3, 2))}
v = lambda i, S: sum(val.get((i, g), 0) for g in S)


def exhaustive(base):
    Bs = [[g for g in range(m) if base[g] == i] for i in range(n)]; Jr = [g for g in range(m) if base[g] < 0]
    for q in itertools.product(range(n), repeat=len(Jr)):
        if sum(q.count(i) >= 2 for i in range(n)) > 1: continue
        X = [list(Bs[i]) + [g for g, a in zip(Jr, q) if a == i] for i in range(n)]
        if all(v(i, X[i]) >= v(i, X[j]) - val.get((i, h), 0) for i in range(n) for j in range(n) if j != i for h in X[j]): return X
    return None


if __name__ == '__main__':
    print('$ python3 kgen/r_cex7.py')
    left = set(range(m)); Y = [None] * n
    for i in order:
        g = next(h for h in rk[i] if h in left); Y[i] = g; left.discard(g)
    ub = upgrade(rk, m, base_of(tuple(Y), m)); B, J, U, NA, F, T = parts(rk, m, ub); t = T[0]
    E = exposed(rk, ub, t, B, J, U); pos = topo(rk, B, U)
    print('rankings', rk, 'm', m, 'order', order, 'picks', Y, 'J', J, 'T', T, 'omega', len(J) - len(T), 'E_t', E,
          'hard:', not lb2(rk, m, base_of(tuple(Y), m)))
    for k in E:
        for P in chains_to(rk, B, U, k, t):
            nb = rotate(rk, ub, B, k, P); P3 = parts(rk, m, upgrade(rk, m, nb))
            print("k = %d, chain %s (Rule E: %s): omega' = %d; lb2 %s; Lemma 1 owner none/k %s; exhaustive: %s" % (
                k, P, P == rule_e_chain(rk, B, U, k, t, pos), len(P3[1]) - len(P3[5]), bool(lb2(rk, m, nb)),
                own_none_or_k(rk, m, nb, k), exhaustive(nb) or 'NONE'))
