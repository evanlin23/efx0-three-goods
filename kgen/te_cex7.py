"""The n = 7 counterexample to T-E's "every k" (found by k3-oc1, `k4/k3_oc1.md` on claude/k4-k3-oc1; checked here):
a ledger-core gap draft with one terminal where one exposed agent's rotation has no one-absorber completion.
For each k in E_t, its Rule E chain (here its only need chain) is rotated; then (1) k3-oc1's exact test lb2,
(2) kgen/k3max_te.py's owner none/t/k test, (3) an exhaustive search over every completion keeping all bases (junk to
agents, at most one agent with two or more junk goods), raw EFX0 with values 4, 3, 2.  At k = 3 a strictly balanced
profile's comparisons are fixed by the rankings, so (3) is exact.  Needs K3OC1 as kgen/k3max_t1.py.

    K3OC1=... python3 kgen/te_cex7.py"""
import sys, os, itertools
K = os.environ.get('K3OC1', os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'k4', 'k3oc1'))
sys.path.insert(0, K); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k3lib import base_of
from lbtest import lb2, parts, exposed, upgrade
from thm_bstar import chains_to
from k3max_t1 import rotate
from k3max_ruleE import topo, rule_e_chain
from k3max_te import complete

rk = [(3, 9, 0), (4, 6, 10), (5, 11, 8), (2, 0, 8), (3, 2, 1), (5, 1, 7), (7, 4, 6)]; m = 12; n = 7
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
    print('$ python3 kgen/te_cex7.py')
    left = set(range(m)); Y = []
    for i in range(n):
        g = next(h for h in rk[i] if h in left); Y.append(g); left.discard(g)
    ub = upgrade(rk, m, base_of(tuple(Y), m)); B, J, U, NA, F, T = parts(rk, m, ub); t = T[0]
    E = exposed(rk, ub, t, B, J, U); pos = topo(rk, B, U)
    print('rankings (a > b > c):', rk, 'm =', m, '; order 0..6, picks', Y, '; J', J, '; T', T, '; E_t', E,
          '; hard at the draft (lb2 fails):', not lb2(rk, m, base_of(tuple(Y), m)))
    for k in E:
        P = rule_e_chain(rk, B, U, k, t, pos); nb = rotate(rk, ub, B, k, P); nbu = upgrade(rk, m, nb)
        r = complete(rk, m, nbu, [None, t], k) or complete(rk, m, nbu, [k], k); X = exhaustive(nb)
        print('k = %d: Rule E chain %s (all need chains: %s); lb2 %s; owner none/t/k: %s; exhaustive: %s'
              % (k, P, chains_to(rk, B, U, k, t), bool(lb2(rk, m, nb)), r, X if X else 'NO ONE-ABSORBER COMPLETION'))
