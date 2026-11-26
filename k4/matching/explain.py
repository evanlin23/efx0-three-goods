"""List every repairing official move of a start, with its description and the owners that complete afterwards.

Moves are enumerated here with descriptions, following the rule of k4/sdc/oc1_mc2_rand.Inst.moves (additions; chains
x_0..x_t, x_i taking B_{x_{i-1}} + H_i, x_0 taking H_0 from the unused junk and B_{x_t}, never handing on an empty
base; rings); the set of resulting states is asserted equal to Inst.moves.  For chains from a dangerous agent with
an end unfrozen at the picks, the exchange value (d, s) of exchange.cm_value is shown.

    python3 k4/matching/explain.py 'SETS' 'VALS' 'PICKS'      (JSON lists)"""
import sys, json, itertools
import _mpaths  # noqa: F401
from mlib import M, INF, subsets
from exchange import cm_value


def described_moves(I, base):
    n = I.n; J = I.junk(base); out = []
    key = lambda nb: tuple(tuple(sorted(b)) for b in nb)
    for x in range(n):
        for H in subsets([g for g in J if g in I.R[x]], 1):
            nb = [list(b) for b in base]; nb[x] = list(base[x]) + list(H); out.append((('add', (x,), {0: H}), nb))

    def ext(path, used, Hs):
        xt = path[-1]
        if len(path) >= 2:
            pool = [g for g in J if g not in used and g in I.R[path[0]]] + [g for g in base[xt] if g in I.R[path[0]]]
            for H0 in subsets(pool, 1):
                if I.V(path[0], H0) > I.V(path[0], base[path[0]]):
                    nb = [list(b) for b in base]; nb[path[0]] = list(H0)
                    for i in range(1, len(path)): nb[path[i]] = list(base[path[i - 1]]) + list(Hs[i])
                    out.append((('chain', tuple(path), {0: H0, **Hs}), nb))
        if len(path) >= n or not base[xt]: return
        for y in range(n):
            if y in path: continue
            for H in subsets([g for g in J if g not in used and g in I.R[y]]):
                if I.V(y, list(base[xt]) + list(H)) > I.V(y, base[y]):
                    ext(path + [y], used | set(H), {**Hs, len(path): H})
    for x in range(n): ext([x], frozenset(), {})
    for r in range(2, n + 1):
        for cyc in itertools.permutations(range(n), r):
            if cyc[0] != min(cyc): continue

            def ring(i, used, Hs):
                if i == r:
                    nb = [list(b) for b in base]
                    for t in range(r): nb[cyc[t]] = list(base[cyc[t - 1]]) + list(Hs[t])
                    out.append((('ring', cyc, dict(Hs)), nb)); return
                w, pred = cyc[i], cyc[i - 1]
                if not base[pred]: return
                for H in subsets([g for g in J if g not in used and g in I.R[w]]):
                    if I.V(w, list(base[pred]) + list(H)) > I.V(w, base[w]): ring(i + 1, used | set(H), {**Hs, i: H})
            ring(0, frozenset(), {})
    assert set(key(nb) for _, nb in out) == set(key(nb) for nb in I.moves(base)), 'move sets differ'
    return out


if __name__ == '__main__':
    sets, vals, Y = json.loads(sys.argv[1]), json.loads(sys.argv[2]), json.loads(sys.argv[3])
    I = M(sets, vals); base = [[g] if g is not None else [] for g in Y]
    print('picks', Y, 'J', I.junk(base), 'frozen', I.frozen(base), 'D', I.dangerous(base), 'holders', I.holders(base))
    print('want arcs', [(i, j) for i in range(I.n) for j in range(I.n) if i != j and base[j] and I.wants(i, base[j][0], base)])
    print('delta_oa', I.deficiency(base, 'oa'), 'per owner', I.owner_deficiency(base, 'oa'))
    fz = set(I.frozen(base)); D = set(I.dangerous(base))
    for (kind, path, Hs), nb in described_moves(I, base):
        ow = [o for o in range(I.n) if I.complete(nb, 0, 'oa', [o]) is not None]
        if not ow: continue
        ows = [o for o in range(I.n) if I.complete(nb, 0, 'ss', [o]) is not None]
        ex = ''
        if kind == 'chain' and path[0] in D and path[-1] not in fz and base[path[-1]]:
            d, s, why = cm_value(I, base, list(path), list(Hs[0]), nb, {i: list(h) for i, h in Hs.items() if i})
            ex = ' EX(d=%s, s=%d, %s)' % ('INF' if d >= INF else d, s, why)
        print(kind, path, {i: list(h) for i, h in Hs.items() if h}, '->', nb, 'owners oa', ow, 'S*', ows,
              'frozen after', I.frozen(nb), ex)
