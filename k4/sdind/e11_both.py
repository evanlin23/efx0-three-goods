"""E11: inserting a 'both' agent (k4/sd_induct.md §5): u holds its top Y_u = a and nobody wants a
(v_i(a) <= v_i(Y_i) for every i != u).  For EVERY one-absorber completion X' of I - u - a (picks of the others, same
junk), the least number of junk moves to a one-absorber completion of I, and explicit repairs:
  B1 : u takes its most valuable junk good of the absorber's bundle (if u is threatened);
  B2 : u takes, among its junk goods of the absorber's bundle whose taking makes u safe, one of least value to the
       absorber o;
  B3 : B2, then if o is threatened by a two-good bundle {Y_j, g_j}, j hands g_j to o (repeat once).
Also the class 'top' (u holds its top, wanted by someone) for comparison.

    python3 k4/sdind/e11_both.py special|screen|suite|cores:FILES:N:SEED [NMAX]"""
import sys, itertools, collections, json, time
import numpy as np
import _paths
from sdilib import Inst, sd, wanted_by, completions, delete, picks_base, bundles_of, efx0, threatened
from e1_delete import load
from e3_suffix import absorber


def thr_by(I, B, i, j):
    vs = [int(I.V[i, g]) for g in B[j]]
    return bool(vs) and sum(vs) - min(vs) > I.val(i, B[i])


def repair(I, Y, J, X, u, rule):
    pb = picks_base(I, Y)
    B = bundles_of(pb, J, X)
    o = absorber(X, I.n)
    if o is None or not thr_by(I, B, u, o): return X
    cand = [t for t in range(len(J)) if X[t] == o and I.V[u, J[t]] > 0]
    if not cand: return None
    if rule == 'B1':
        t = max(cand, key=lambda t: (I.V[u, J[t]], -J[t]))
    else:
        safe = []
        for t in cand:
            X2 = X.copy(); X2[t] = u
            B2 = bundles_of(pb, J, X2)
            if not thr_by(I, B2, u, o): safe.append(t)
        if not safe: return None
        t = min(safe, key=lambda t: (I.V[o, J[t]], -I.V[u, J[t]], J[t]))
    X2 = X.copy(); X2[t] = u
    if rule == 'B3':
        for _ in range(2):
            B2 = bundles_of(pb, J, X2)
            js = [j for j in threatened(I, B2, o) if j != o and len(B2[j]) == 2 and j != u]
            if not js: break
            j = js[0]; tj = [s for s in range(len(J)) if X2[s] == j][0]; X2[tj] = o
    return X2


if __name__ == '__main__':
    src = sys.argv[1]; NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    C = collections.Counter(); t0 = time.time(); shown = collections.Counter()
    print('$ python3 k4/sdind/e11_both.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src):
        if len(sets) > NMAX or len(sets) < 2: continue
        I = Inst(sets, vals, m); C['instances'] += 1
        seen = set()
        for o_ in itertools.permutations(range(I.n)):
            Y = list(sd(I, o_)[0])
            if tuple(Y) in seen: continue
            seen.add(tuple(Y))
            try:
                J, A = completions(I, picks_base(I, Y), 1)
            except ValueError:
                continue
            W = wanted_by(I, Y)
            Aset = set(map(tuple, A.tolist()))
            for u in range(I.n):
                if Y[u] is None or Y[u] != max(I.R[u], key=lambda h: (I.V[u, h], -h)): continue
                cls = 'both' if not W[u] else 'top (wanted)'
                I2, amap, gmap = delete(I, [u], [Y[u]])
                inv = {b: a for a, b in amap.items()}
                Y2 = [None] * I2.n
                for a, b in amap.items(): Y2[b] = gmap[Y[a]] if Y[a] is not None else None
                J2, A2 = completions(I2, picks_base(I2, Y2), 1)
                C[cls + ': cases'] += 1
                C[cls + ': A(I) empty'] += (len(A) == 0)
                C[cls + ': A(sub) empty'] += (len(A2) == 0)
                if len(A2) and len(A) == 0:
                    C[cls + ': SUB EXTENDS BUT I DOES NOT'] += 1
                    if shown[cls + 'x'] < 3:
                        shown[cls + 'x'] += 1
                        print('SUB EXTENDS, I NOT', cls, name, json.dumps((sets, vals)), 'picks', Y, 'u', u, flush=True)
                for x2 in A2:
                    X = np.array([inv[b] for b in x2], dtype=np.int64)
                    d = int((A != X[None, :]).sum(axis=1).min()) if len(A) and len(J) else (0 if len(A) else None)
                    C[cls + ': X\' least distance %s' % d] += 1
                    for rule in ('B1', 'B2', 'B3'):
                        Z = repair(I, Y, J, X, u, rule)
                        ok = Z is not None and tuple(Z.tolist()) in Aset
                        C[cls + ': rule %s works' % rule] += ok
                        if not ok and rule == 'B3' and cls == 'both' and shown[rule] < 4:
                            shown[rule] += 1
                            print('B3 FAILS', name, json.dumps((sets, vals)), 'picks', Y, 'u', u, 'X\'', dict(zip(J, X.tolist())),
                                  'least d', d, flush=True)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
