"""E15: the 'u is the sink' repair for inserting a both agent u (free completions; k4/sd_induct.md §5).
Start from X' + u{Y_u}.  Repeat: if u is threatened by a bundle B_k, u takes its most valuable junk good of B_k;
else if some agent i != u is threatened by a two-good bundle {Y_k, g} (k != u), g moves to u; else if i is threatened
by a bundle B_k with >= 3 goods (k != u), i's most valuable junk good of B_k moves to u; else stop.  Junk only moves
to u, so this stops.  Success: the result is EFX0.  Failure modes recorded: an agent threatened by u's bundle; nothing
left to move.

    python3 k4/sdind/e15_sink.py special|screen|suite|cores:FILES:N:SEED [NMAX]"""
import sys, itertools, collections, json, time
import numpy as np
import _paths
from sdilib import Inst, sd, wanted_by, completions, delete, picks_base, bundles_of, efx0, threatened
from e1_delete import load


def sink(I, Y, J, X, u):
    pb = picks_base(I, Y); Z = X.copy(); jidx = {g: t for t, g in enumerate(J)}
    for it in range(len(J) + 2):
        B = bundles_of(pb, J, Z)
        th = threatened(I, B, u)
        if th:
            k = th[0]; cand = [g for g in B[k] if g in jidx and I.V[u, g] > 0]
            if not cand: return Z, 'u threatened, nothing to take'
            g = max(cand, key=lambda g: (I.V[u, g], -g)); Z[jidx[g]] = u; continue
        moved = False
        for i in range(I.n):
            if i == u: continue
            for k in threatened(I, B, i):
                if k == u: continue
                if len(B[k]) == 2:
                    g = [h for h in B[k] if h in jidx][0]; Z[jidx[g]] = u; moved = True; break
                cand = [g for g in B[k] if g in jidx and I.V[i, g] > 0]
                if cand:
                    g = max(cand, key=lambda g: (I.V[i, g], -g)); Z[jidx[g]] = u; moved = True; break
            if moved: break
        if not moved:
            return Z, ('ok' if efx0(I, B) else 'threatened by u')
    return Z, 'loop'


if __name__ == '__main__':
    src = sys.argv[1]; NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    C = collections.Counter(); t0 = time.time(); shown = collections.Counter()
    print('$ python3 k4/sdind/e15_sink.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src):
        if len(sets) > NMAX or len(sets) < 2: continue
        I = Inst(sets, vals, m); seen = set(); C['instances'] += 1
        for o_ in itertools.permutations(range(I.n)):
            Y = list(sd(I, o_)[0])
            if tuple(Y) in seen: continue
            seen.add(tuple(Y)); W = wanted_by(I, Y)
            both = [u for u in range(I.n) if Y[u] is not None and not W[u] and Y[u] == max(I.R[u], key=lambda h: (I.V[u, h], -h))]
            if not both: continue
            J = sorted(set(range(I.m)) - set(g for g in Y if g is not None))
            if I.n ** len(J) > 2_000_000: continue
            for u in both:
                I2, amap, gmap = delete(I, [u], [Y[u]]); inv = {b: a for a, b in amap.items()}
                Y2 = [None] * I2.n
                for a, b in amap.items(): Y2[b] = gmap[Y[a]] if Y[a] is not None else None
                J2, A2 = completions(I2, picks_base(I2, Y2), None)
                if len(A2) == 0: continue
                C['cases'] += 1; allok = True
                for x2 in A2:
                    X = np.array([inv[b] for b in x2], dtype=np.int64)
                    Z, res = sink(I, Y, J, X, u)
                    C['X\': ' + res] += 1; allok &= (res == 'ok')
                    if res != 'ok' and shown[res] < 3:
                        shown[res] += 1
                        print('SINK', res, name, json.dumps((sets, vals)), 'picks', Y, 'u', u, 'X\'',
                              bundles_of(picks_base(I, Y), J, X), '->', bundles_of(picks_base(I, Y), J, Z), flush=True)
                C['cases: sink works from every X\''] += allok
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
