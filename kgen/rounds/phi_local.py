"""The local step of a minimal-counterexample proof of Φ-MAX (kgen/rounds.md §4.12): for every MD EFX0 allocation X
that is NOT a witness of a round of OC1' moves, the nearest MD EFX0 allocation X' with Φ(X') > Φ(X) (fewest goods
changing owner), and what the change is when one or two goods move.  Random strict connected cores, every perfect start.
    python3 kgen/rounds/phi_local.py n,m,count,seed"""
import sys, os, json, collections, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import rndlib, recs_vs_rndp as RV
from splice_search import rows_of, dense
from rndp_structure import shapes


def phi(V, y, X, o):
    n = len(V); picks = set(y)
    npk = [sum(1 for g in X[a] if g in picks) for a in range(n)]
    return (sum(1 for a in range(n) if npk[a] == 1), -sum(1 for a in range(n) if sum(1 for g in X[a] if g not in picks) >= 2))


C = collections.Counter(); ex = collections.defaultdict(list); t0 = time.time()
for row in rows_of('random', sys.argv[1], 1):
    V = dense(row['sets'], row['vals']); n, m = len(V), len(V[0]); y = tuple(row['picks']); p = [V[a][y[a]] for a in range(n)]
    alls, _ = rndlib.list_efx(V); md = []
    for o in alls:
        X = [[g for g in range(m) if o[g] == i] for i in range(n)]
        if any(sum(V[a][g] for g in X[a]) < p[a] for a in range(n)): continue
        md.append((o, X, phi(V, y, X, o), bool(RV.structures(V, y, X, False))))
    for o, X, ph, w in md:
        if w: continue
        f = [o[y[a]] for a in range(n)]; sh = tuple(sorted(s for s in shapes(f, n) if s != 'fixed'))
        better = [(sum(1 for g in range(m) if o[g] != o2[g]), o2, ph2) for o2, X2, ph2, w2 in md if ph2 > ph]
        C[('non-witness', sh)] += 1
        if not better: C[('NO BETTER Φ', sh)] += 1; continue
        d, o2, ph2 = min(better)
        C[('distance to better Φ', d)] += 1
        if d <= 2:
            moved = [(g, o[g], o2[g], 'pick of %d' % y.index(g) if g in y else 'junk') for g in range(m) if o[g] != o2[g]]
            # describe: does the move give a pickless agent back its pick, or move a pick off a keeper
            kind = []
            for g, a, b, what in moved:
                if g in y:
                    owner = y.index(g)
                    kind.append('pick %s: %s -> %s' % ('to its owner' if b == owner else 'off its owner' if a == owner else 'between others',
                                                       'keeper' if o[y[a]] == a else 'mover', 'owner' if b == owner else 'keeper' if o[y[b]] == b else 'mover'))
                else: kind.append('junk')
            C[('move at distance %d' % d, tuple(sorted(kind)))] += 1
            if len(ex[d]) < 2: ex[d].append({'V': V, 'picks': y, 'X': X, 'X2': [[g for g in range(m) if o2[g] == i] for i in range(n)], 'shapes': sh})
for k in sorted(C, key=str): print(k, C[k])
for d, v in ex.items():
    for e in v: print('example distance', d, json.dumps(e))
print('time %.0f s' % (time.time() - t0))
