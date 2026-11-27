"""Replay of d1's k = 4 counterexample to the every-order form of Conjecture RF (K4.SDC.RF), n = 5, 5_pure #440
(m = 8): agents 3 and 4 are SET-twins (same relevant goods, different values).  At the OC1-failing maximum-matching
start Y = (3,6,7,4,5) the unique receiver is 4; the 4-first order (4,0,1,2,3) gives Y' = (3,6,7,5,4), the twins' picks
swapped, where OC1 fails again.  RF-exists (some 4-first maximum-matching vector satisfies OC1) and RF-rot-exists (some
rotation (4, o - 4) of an order o giving Y satisfies OC1) hold.  Raw checker oc1_mc2_rand.Inst.check (coordinator's
code; d1's three checkers are k4/rf_indep/verify_rf_every_cex.py).
    python3 k4/sdc/rf_k4_settwin_cex.py"""
import itertools
import _paths  # noqa: F401
from oc1_mc2_rand import Inst
from oc1_max_orders import nu

SETS = [[0, 3, 5, 7], [1, 2, 3, 6], [1, 2, 6, 7], [4, 5, 6, 7], [4, 5, 6, 7]]
VALS = [[5, 19, 13, 10], [9, 6, 17, 12], [3, 5, 7, 6], [14, 1, 7, 4], [18, 4, 11, 5]]

if __name__ == '__main__':
    print('$ python3 k4/sdc/rf_k4_settwin_cex.py')
    for i, v in enumerate(VALS):
        sums = [sum(c) for r in range(1, 5) for c in itertools.combinations(v, r)]
        print('agent', i, 'strict (all 15 nonempty subset sums distinct):', len(sums) == len(set(sums)))
    I = Inst(SETS, VALS); n = I.n; N = nu(I); Y = (3, 6, 7, 4, 5)
    ords = [o for o in itertools.permutations(range(n)) if I.sd(o) == Y]
    print('sets', SETS, 'vals', VALS, 'nu', N)
    print('Y', Y, 'orders giving Y', ords, '->', I.check(Y))
    rec = [u for u in range(n) if Y[u] is not None and all(I.v[i].get(Y[u], 0) <= I.v[i].get(Y[i], 0) for i in range(n) if i != u)]
    print('receivers', rec)
    every = True; some = False
    for u in rec:
        seen = set()
        for rest in itertools.permutations([i for i in range(n) if i != u]):
            p = I.sd((u,) + rest)
            if p in seen: continue
            seen.add(p); mm = sum(x is not None for x in p) == N; r = I.check(p)
            print('  u-first order', (u,) + rest, 'picks', p, 'max' if mm else 'non-max', r)
            if mm: every &= r != 'OC1 fails'; some |= r != 'OC1 fails'
        rot = {}
        for o in ords:
            p = I.sd((u,) + tuple(i for i in o if i != u)); rot[p] = I.check(p)
        print('  rotations (u, o - u):', rot)
        print('  RF-rot-exists:', 'holds' if any(r != 'OC1 fails' for r in rot.values()) else 'FAILS')
    print('RF every-form:', 'holds' if every else 'FAILS', '| RF-exists:', 'holds' if some else 'FAILS')
