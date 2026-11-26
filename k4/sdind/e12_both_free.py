"""E12: Lemma BOTH for the FREE completion (any number of absorbers) (k4/sd_induct.md §5).  u holds its top and
nobody wants it.  For every EFX0 completion X' (free) of the picks of I - u - Y_u: least Hamming distance to an EFX0
completion of I (free); and the explicit repair FB: while u is threatened by some bundle with >= 3 goods, u takes its
most valuable junk good of that bundle (at most |R_u| - 1 = 3 times) -- then check EFX0.

    python3 k4/sdind/e12_both_free.py special|screen|suite|cores:FILES:N:SEED [NMAX]"""
import sys, itertools, collections, json, time
import numpy as np
import _paths
from sdilib import Inst, sd, wanted_by, completions, delete, picks_base, bundles_of, efx0, threatened
from e1_delete import load

if __name__ == '__main__':
    src = sys.argv[1]; NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    C = collections.Counter(); t0 = time.time(); shown = collections.Counter()
    print('$ python3 k4/sdind/e12_both_free.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src):
        if len(sets) > NMAX or len(sets) < 2: continue
        I = Inst(sets, vals, m); C['instances'] += 1
        seen = set()
        for o_ in itertools.permutations(range(I.n)):
            Y = list(sd(I, o_)[0])
            if tuple(Y) in seen: continue
            seen.add(tuple(Y))
            W = wanted_by(I, Y)
            both = [u for u in range(I.n) if Y[u] is not None and not W[u] and Y[u] == max(I.R[u], key=lambda h: (I.V[u, h], -h))]
            if not both: continue
            try:
                J, A = completions(I, picks_base(I, Y), None)
            except ValueError:
                C['skipped'] += 1; continue
            Aset = set(map(tuple, A.tolist())); pb = picks_base(I, Y)
            for u in both:
                I2, amap, gmap = delete(I, [u], [Y[u]])
                inv = {b: a for a, b in amap.items()}
                Y2 = [None] * I2.n
                for a, b in amap.items(): Y2[b] = gmap[Y[a]] if Y[a] is not None else None
                J2, A2 = completions(I2, picks_base(I2, Y2), None)
                C['cases'] += 1; C['A(I) empty'] += (len(A) == 0); C['A(sub) empty'] += (len(A2) == 0)
                if len(A2) and not len(A):
                    C['SUB EXTENDS BUT I DOES NOT'] += 1
                    print('FREE BOTH FAILS', name, json.dumps((sets, vals)), 'picks', Y, 'u', u, flush=True)
                for x2 in A2:
                    X = np.array([inv[b] for b in x2], dtype=np.int64)
                    d = int((A != X[None, :]).sum(axis=1).min()) if len(A) and len(J) else (0 if len(A) else None)
                    C['X\' least distance %s' % d] += 1
                    C['|R_u| = %d: X\' least distance %s' % (len(I.R[u]), d)] += 1
                    Z = X.copy()
                    for _ in range(3):
                        B = bundles_of(pb, J, Z)
                        th = [j for j in threatened(I, B, u) if len(B[j]) >= 3]
                        if not th: break
                        j = th[0]
                        cand = [t for t in range(len(J)) if Z[t] == j and I.V[u, J[t]] > 0]
                        if not cand: break
                        t = max(cand, key=lambda t: (I.V[u, J[t]], -J[t])); Z[t] = u
                    ok = tuple(Z.tolist()) in Aset
                    C['FB works'] += ok
                    if not ok and shown['fb'] < 3:
                        shown['fb'] += 1
                        print('FB FAILS', name, json.dumps((sets, vals)), 'picks', Y, 'u', u, 'X\'', dict(zip(J, X.tolist())), 'least d', d, flush=True)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
