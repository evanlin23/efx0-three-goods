"""Replay of the k = 5 refutations of the RKMAX form (ksens N3K5, kgen-n3 n3_m6_93; k4/sdc.md §31, K4.SDC.RKMAX.K5).
At n = 3, when the three agents share their two top goods, every SD vector has signature (1, 1, 1, 0, 0): the first
picker gets rank 1, the second rank 2, the third rank 3. So "OC1 at every sigma-maximal vector" reduces to OC1^max,
which fails at k = 5.  Ranks here run to k (no rank cap); OC1 by the raw checker oc1_mc2_rand.Inst.check.
    python3 k4/sdc/rkmax_k5_cex.py"""
import itertools
import _paths  # noqa: F401
from oc1_mc2_rand import Inst
from oc1_max_orders import nu

CASES = {
    'N3K5 (ksens)': ([[0, 2, 3, 4, 5], [1, 2, 3, 4, 5], [1, 4, 5]], [[3, 22, 23, 38, 43], [15, 17, 27, 40, 43], [1, 2, 4]]),
    'n3_m6_93 (kgen-n3)': ([[0, 2, 3, 4, 5], [1, 2, 3, 4, 5], [1, 3, 4, 5]], [[3, 33, 39, 35, 43], [16, 20, 32, 26, 43], [3, 6, 2, 10]]),
}

if __name__ == '__main__':
    print('$ python3 k4/sdc/rkmax_k5_cex.py')
    for name, (sets, vals) in CASES.items():
        I = Inst(sets, vals); n = I.n; N = nu(I); K = max(len(s) for s in sets)
        vec = {}
        for o in itertools.permutations(range(n)): vec.setdefault(I.sd(o), []).append(o)
        rows = []
        for p, os in vec.items():
            if sum(x is not None for x in p) != N: continue
            r = tuple(1 + sum(1 for g in I.R[i] if I.v[i][g] > I.v[i][p[i]]) for i in range(n))
            sig = tuple(sum(1 for x in r if x == t) for t in range(1, K + 1))
            rows.append((sig, p, os, r, I.check(p)))
        best = max(x[0] for x in rows)
        print(name, 'k =', K, 'sets', sets, 'vals', vals)
        for sig, p, os, r, res in rows:
            print('  picks', p, 'orders', os, 'ranks', r, 'sigma', sig, 'sigma-max' if sig == best else '', res)
        bad = [x for x in rows if x[0] == best and x[4] == 'OC1 fails']
        print('  RKMAX form', 'FAILS at', [x[1] for x in bad] if bad else 'holds')
