"""The n = 7 counterexample to T1-k and to Conjecture R-omega (kgen/n3.md §15.19; found by k3-oc1,
attempts/k4-k3oc1-tprime-k.md on claude/k4-k3-oc1; replayed here independently).  A one-terminal gap draft of an
m = 11 ledger core whose two exposed agents are twins (same pair, containing Y_t).  For every rotation into t (every
need chain from every k in E_t): omega' after LB's upgrades; this note's owner none/k test (kgen/k3max_owner.py);
Lemma 3 for owner t (kgen/k3max_propB.py's criterion); and an exhaustive search over every completion of the rotated
bases (raw EFX0, values 4, 3, 2), listing the agents that receive two or more junk goods.  Needs K3OC1.

    K3OC1=... python3 kgen/tk_cex7.py"""
import sys, os, itertools, collections
K = os.environ.get('K3OC1', os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'k4', 'k3oc1'))
sys.path.insert(0, K); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k3lib import base_of
from lbtest import lb2, parts, exposed, upgrade
from thm_bstar import chains_to, mh
from k3max_t1 import rotate
from k3max_ruleE import rule_e_chain
from k3max_owner import own_none_or_k
from k3max_propB import topo_last

rk = [(7, 0, 8), (5, 7, 9), (5, 10, 7), (0, 3, 2), (1, 2, 6), (1, 6, 4), (3, 4, 6)]; m = 11; n = 7
order = (2, 1, 0, 5, 6, 3, 4)
val = {(i, g): x for i in range(n) for g, x in zip(rk[i], (4, 3, 2))}
v = lambda i, S: sum(val.get((i, g), 0) for g in S)


def completions(base):
    """every EFX0 completion of the bases; returns the multiset of absorber sets (agents with >= 2 junk goods)"""
    Bs = [[g for g in range(m) if base[g] == i] for i in range(n)]; Jr = [g for g in range(m) if base[g] < 0]
    A = collections.Counter(); ex = {}
    for q in itertools.product(range(n), repeat=len(Jr)):
        X = [list(Bs[i]) + [g for g, a in zip(Jr, q) if a == i] for i in range(n)]
        if all(v(i, X[i]) >= v(i, X[j]) - val.get((i, h), 0) for i in range(n) for j in range(n) if j != i for h in X[j]):
            ab = tuple(i for i in range(n) if q.count(i) >= 2); A[ab] += 1; ex.setdefault(ab, X)
    return A, ex


def lemma3_t(base, t):
    B2, J2, U2, NA2, F2, T2 = parts(rk, m, base)
    if t not in T2: return False
    Eo = exposed(rk, base, t, B2, J2, U2); Ef = [y for y in Eo if y in F2]
    return mh([[h for h in rk[y][1:] if h in J2] for y in Ef]) <= len([z for z in T2 if z not in Eo]) - 1


if __name__ == '__main__':
    print('$ python3 kgen/tk_cex7.py')
    left = set(range(m)); Y = [None] * n
    for i in order:
        g = next(h for h in rk[i] if h in left); Y[i] = g; left.discard(g)
    b0 = base_of(tuple(Y), m); ub = upgrade(rk, m, b0); B, J, U, NA, F, T = parts(rk, m, ub); t = T[0]
    E = exposed(rk, ub, t, B, J, U); pos = topo_last(rk, B, U, t)
    print('rankings', rk, 'm', m, 'order', order, 'picks', Y, 'upgrades at the draft', ub != b0, 'J', J, 'T', T,
          'omega', len(J) - len(T), 'E_t', E, 'pairs', {x: sorted(rk[x][1:]) for x in E}, 'hard (lb2 fails):', not lb2(rk, m, b0))
    A0, _ = completions(b0); print('one-absorber completions of the picks:', sum(c for a, c in A0.items() if len(a) <= 1))
    for k in E:
        for P in chains_to(rk, B, U, k, t):
            nb = rotate(rk, ub, B, k, P); P3 = parts(rk, m, upgrade(rk, m, nb)); A, ex = completions(nb)
            one = {a: c for a, c in A.items() if len(a) <= 1}
            print("k = %d, chain %s (Rule E, t last: %s): omega' = %d; owner none/k (Lemma 1) %s; Lemma 3 owner t %s; lb2 %s"
                  % (k, P, P == rule_e_chain(rk, B, U, k, t, pos), len(P3[1]) - len(P3[5]), own_none_or_k(rk, m, nb, k),
                     lemma3_t(nb, t), bool(lb2(rk, m, nb))))
            print('   one-absorber EFX0 completions by absorber set:', dict(sorted(one.items())), '; examples:',
                  {a: ex[a] for a in sorted(one)})
