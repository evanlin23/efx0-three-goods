"""The family behind attempts/k4-k3oc1-oc1-counterexample.md: q agents x_j each holding its top t_j with a private pair
(two goods nobody else values), and p agents that value only tops and get nothing (they come last).  Each top must be
wanted by an empty-handed agent.  For given (p, q) and top sets of the empty-handed agents: does one chain (with or
without glue) give a one-absorber completion?
    python3 k4/k3oc1/glue_family.py"""
import sys, os, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import sd, base_of, completion, chains, vals
from lbtest import lb2

def build(p, q, E_sets):
    rk = []
    for j in range(q):
        rk.append((j, q + 2 * j, q + 2 * j + 1))          # x_j: top t_j = good j, private pair
    for S in E_sets: rk.append(tuple(S))                   # empty-handed agents value tops only
    return rk, 3 * q

for p, q, E_sets in [(2, 3, [(0, 1, 2), (0, 1, 2)]), (2, 4, [(0, 1, 2), (1, 2, 3)]), (2, 4, [(0, 1, 2), (3, 0, 1)]),
                     (3, 4, [(0, 1, 2), (1, 2, 3), (2, 3, 0)]), (3, 5, [(0, 1, 2), (2, 3, 4), (4, 0, 1)]),
                     (2, 5, [(0, 1, 2), (2, 3, 4)]), (3, 6, [(0, 1, 2), (3, 4, 5), (0, 3, 5)])]:
    rk, m = build(p, q, E_sets); n = len(rk); V = vals(rk)
    order = list(range(n))   # x's first, then the empty-handed agents
    Y = sd(rk, m, order); b = base_of(Y, m)
    assert all(Y[q + i] is None for i in range(p)), Y
    # every state here is a DE state (singles and private pairs {b, c}), where lb2 is exact (xcheck_lb2_*.log)
    def is_de(st):
        from k3lib import bundles
        return all(not B or (len(B) == 1 and B[0] in rk[i]) or set(B) == {rk[i][1], rk[i][2]} for i, B in enumerate(bundles(st, n)))
    if m <= 12: test = lambda st: completion(rk, m, st, 1, V) is not None
    else: test = lambda st: is_de(st) and bool(lb2(rk, m, st))   # chains to non-DE states are skipped (marked below)
    c0 = test(b)
    ng = any(test(nb) for nb, d in chains(rk, m, b, V))
    gl = any(test(nb) for nb, d in chains(rk, m, b, V, glue=True))
    print('p=%d q=%d E=%s: picks %s, one chain %s, one glued chain %s%s' % (p, q, E_sets, c0, ng, gl, '' if m <= 12 else ' (m > 12: only chains to DE states tested)'), flush=True)
