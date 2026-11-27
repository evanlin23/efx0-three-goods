"""Replay of ksens's RF5 instance (k = 5, n = 4): the every-order form of Conjecture RF fails, RF-exists survives
(k4/sdc.md §31, ledger K4.SDC.RF.K5EVERY).  Agents 2 and 3 are twins.  At the failing maximum-matching start
Y = (6,5,4,3) the unique receiver is 2; of the six 2-first orders, (2,1,0,3) gives Z = (6,5,3,4), Y with the twins'
picks swapped, where OC1 fails again; the other five 2-first vectors satisfy OC1.  Raw checker oc1_mc2_rand.Inst.check.
    python3 k4/sdc/rf_k5_twin_cex.py"""
import itertools
import _paths  # noqa: F401
from oc1_mc2_rand import Inst
from oc1_max_orders import nu

SETS = [[0, 1, 2, 5, 6], [1, 2, 4, 5, 6], [3, 4, 5, 6], [3, 4, 5, 6]]
VALS = [[3, 35, 33, 43, 39], [20, 26, 16, 43, 32], [8, 2, 7, 4], [8, 2, 7, 4]]

if __name__ == '__main__':
    print('$ python3 k4/sdc/rf_k5_twin_cex.py')
    I = Inst(SETS, VALS); n = I.n; N = nu(I); Y = (6, 5, 4, 3)
    print('sets', SETS, 'vals', VALS, 'nu', N)
    print('Y', Y, 'orders', [o for o in itertools.permutations(range(n)) if I.sd(o) == Y], I.check(Y))
    rec = [u for u in range(n) if Y[u] is not None and all(I.v[i].get(Y[u], 0) <= I.v[i].get(Y[i], 0) for i in range(n) if i != u)]
    print('receivers', rec)
    every = True; some = False
    for u in rec:
        seen = set()
        for rest in itertools.permutations([i for i in range(n) if i != u]):
            p = I.sd((u,) + rest)
            if p in seen: continue
            seen.add(p); mm = sum(x is not None for x in p) == N; r = I.check(p)
            print('  order', (u,) + rest, 'picks', p, 'max' if mm else 'non-max', r)
            if mm: every &= r != 'OC1 fails'; some |= r != 'OC1 fails'
    print('RF every-form:', 'holds' if every else 'FAILS', '| RF-exists:', 'holds' if some else 'FAILS')
