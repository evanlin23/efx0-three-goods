"""Smallest instances where OPB-AACGMM version 2 (kgen/aacgmm3_opb2.py; flags RECHOOSE, DUMPSWAP from the environment)
fails, per failure type, with small integer values made non-degenerate as in kgen/aacgmm3.py.  For each, also whether
an OC1 completion with one pick per bundle exists (brute force).  Also the smallest start where no role assignment ends
in an OC1 completion.

    [RECHOOSE=1] [DUMPSWAP=1] python3 kgen/aacgmm3_opb2_min.py SEED N"""
import sys, random, itertools, collections, json
from lemmaT3 import reachable
from oc3lib import picks, ORD
from aacgmm3 import efx0
from aacgmm3_opb import Stuck
import aacgmm3_opb2 as O

if __name__ == '__main__':
    seed, N = map(int, sys.argv[1:3]); rng = random.Random(seed); best = {}; stats = collections.Counter()
    print('$ %s%spython3 kgen/aacgmm3_opb2_min.py' % ('RECHOOSE=1 ' if O.RECHOOSE else '', 'DUMPSWAP=1 ' if O.DUMPSWAP else ''), *sys.argv[1:], flush=True)
    for t in range(N):
        m = rng.randint(3, 7); hi = rng.choice([3, 5, 9])
        raw = [[rng.choice([0] * (t % 2) + list(range(1, hi + 1))) for _ in range(m)] for _ in range(3)]
        V = [[raw[i][j] * 2 ** (m + 1) + 2 ** j for j in range(m)] for i in range(3)]
        for o in ORD:
            y = picks(V, o)
            if any(g is None for g in y): continue
            anyok = False
            for roles in ORD:
                try:
                    X, it = O.opb2(V, roles, y, stats)
                    if reachable(V, y, X): anyok = True; continue
                    key = 'ends EFX0 but not OC1 (identity placement)' if all(y[i] in X[i] for i in range(3)) else 'ends EFX0 but not OC1 (a receiver does not gain)'
                except Stuck as e: key = str(e)
                size = (m, sum(map(sum, raw)))
                if key not in best or size < best[key][0]: best[key] = (size, raw, o, roles, y)
            if not anyok:
                key = 'START WHERE NO ROLE ASSIGNMENT ENDS IN AN OC1 COMPLETION'; size = (m, sum(map(sum, raw)))
                if key not in best or size < best[key][0]: best[key] = (size, raw, o, None, y)
    for key, (size, raw, o, roles, y) in sorted(best.items()):
        m = len(raw[0]); V = [[raw[i][j] * 2 ** (m + 1) + 2 ** j for j in range(m)] for i in range(3)]; P = set(y)
        allX = [[{g for g in range(m) if q[g] == i} for i in range(3)] for q in itertools.product(range(3), repeat=m)]
        opbX = [X for X in allX if efx0(V, X) and reachable(V, y, X) and all(len(B & P) == 1 for B in X)]
        print('%s: m = %d, values %s, order %s, roles %s, picks %s; an OC1 completion with one pick per bundle: %s'
              % (key, m, json.dumps(raw), o, roles, y, [sorted(b) for b in opbX[0]] if opbX else 'NONE'))
