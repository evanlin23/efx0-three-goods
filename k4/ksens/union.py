"""Attempt (attempts/k4-ksens-union.md): two disjoint copies of the dichotomy counterexample K4.SDC.DICH (k4/sdc.md §29,
n = 3, k = 4) to force two absorbers at k = 4.  Prints the single instance's status and the union's, with the
one-chain completion found.

    python3 k4/ksens/union.py"""
import json
import _paths
import ocsat

SETS = [[0, 2, 4, 3], [6, 3, 1], [1, 2, 0, 5]]; VALS = [[5, 10, 1, 12], [10, 12, 11], [11, 8, 6, 1]]; M = 7

if __name__ == '__main__':
    O = ocsat.OC(SETS, VALS, M); Y = ocsat.sd(SETS, VALS, (0, 2, 1), M); b = ocsat.bases_of(Y, 3)
    print('single (K4.SDC.DICH):', json.dumps((SETS, VALS)), 'order (0, 2, 1) picks', Y)
    print('   one-absorber completion', O.holds(b, chain='none', A=1), '; none without absorber', O.holds(b, chain='none', A=0),
          '; one chain then one absorber', O.holds(b, chain='need', A=1), '; one chain then no absorber', O.holds(b, chain='need', A=0))
    S2 = SETS + [[g + M for g in s] for s in SETS]; V2 = VALS + VALS
    O2 = ocsat.OC(S2, V2, 2 * M); Y2 = ocsat.sd(S2, V2, (0, 2, 1, 3, 5, 4), 2 * M); b2 = ocsat.bases_of(Y2, 6)
    print('union (n = 6, m = 14): order (0, 2, 1, 3, 5, 4) picks', Y2)
    print('   one-absorber completion of the picks', O2.holds(b2, chain='none', A=1))
    X, nb = O2.holds(b2, chain='need', A=1, model=True)
    print('   one chain then one absorber: True; bundles', X, 'new bases', nb)
    res = ocsat.report(S2, V2, 2 * M, orders=[(0, 2, 1, 3, 5, 4), (3, 5, 4, 0, 2, 1), (0, 2, 3, 5, 1, 4)])
    for Yy, r in res.items(): print('   order', r['order'], r)
