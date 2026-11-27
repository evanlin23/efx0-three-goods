"""The smallest failure of T1-P's branch "no junk-pair k, so every k works" (kgen/n3.md §15.15; found by k3-oc1 in the
exhaustive mixed n = 5 class with one dead good): two exposed agents with the same pair {0, 2}, which contains Y_t.
Checked with lb2 and an exhaustive completion search (raw EFX0, values 4, 3, 2).  Needs K3OC1 as kgen/k3max_t1.py.

    K3OC1=... python3 kgen/te_cex5dead.py"""
import sys, os, itertools
K = os.environ.get('K3OC1', os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'k4', 'k3oc1'))
sys.path.insert(0, K); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k3lib import base_of
from lbtest import lb2, parts, exposed, upgrade
from k3max_t1 import rotate
from k3max_ruleE import topo, rule_e_chain

rk = [(1, 0, 2), (3, 1, 0), (4, 0, 2), (5, 1, 6), (4, 5, 3)]; m = 8; n = 5          # good 7 is dead
order = (0, 2, 3, 4, 1)
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
    print('$ python3 kgen/te_cex5dead.py')
    left = set(range(m)); Y = [None] * n
    for i in order:
        g = next(h for h in rk[i] if h in left); Y[i] = g; left.discard(g)
    ub = upgrade(rk, m, base_of(tuple(Y), m)); B, J, U, NA, F, T = parts(rk, m, ub); t = T[0]
    E = exposed(rk, ub, t, B, J, U); pos = topo(rk, B, U)
    print('rankings', rk, 'm', m, '(good 7 dead); order', order, 'picks', Y, 'J', J, 'T', T, 'E_t', E,
          'pairs', [rk[x][1:] for x in E], 'hard:', not lb2(rk, m, base_of(tuple(Y), m)))
    for k in E:
        P = rule_e_chain(rk, B, U, k, t, pos); nb = rotate(rk, ub, B, k, P); P3 = parts(rk, m, upgrade(rk, m, nb))
        print("k = %d: Rule E chain %s, omega' = %d, lb2 %s, exhaustive: %s" % (k, P, len(P3[1]) - len(P3[5]), bool(lb2(rk, m, nb)), exhaustive(nb) or 'NO ONE-ABSORBER COMPLETION'))
