"""Lemma UNTANGLE data (kgen/rounds.md §4.13): at every non-witness MD EFX0 allocation of random strict cores (all keep-and-add:
q pickless, its pick Y_q with a keeper v), whether returning Y_q to q is EFX0, which EFX0 constraints fail if not,
and which single junk move (from / to: q, v, other) then repairs it.
    python3 kgen/rounds/untangle_roles.py n,m,count,seed"""
import sys, os, json, collections
sys.path.insert(0, 'kgen/rounds')
import rndlib, recs_vs_rndp as RV, verify_k4zero as VZ
from splice_search import rows_of, dense
from rndp_structure import shapes
from phi_local import phi
cfg = sys.argv[1]; C = collections.Counter()
for row in rows_of('random', cfg, 1):
    V = dense(row['sets'], row['vals']); n, m = len(V), len(V[0]); y = tuple(row['picks']); p = [V[a][y[a]] for a in range(n)]; picks = set(y)
    alls, _ = rndlib.list_efx(V); md = []
    for o in alls:
        X = [[g for g in range(m) if o[g] == i] for i in range(n)]
        if any(sum(V[a][g] for g in X[a]) < p[a] for a in range(n)): continue
        md.append((o, X, phi(V, y, X, o), bool(RV.structures(V, y, X, False))))
    for o, X, ph, w in md:
        if w: continue
        f = [o[y[a]] for a in range(n)]
        # the needy ka pair: q pickless, v = f(q) keeper
        qs = [a for a in range(n) if not any(g in picks for g in X[a]) and f[f[a]] == f[a] and f[a] != a]
        if not qs: C['non-witness without a ka pair'] += 1; continue
        q = qs[0]; v = f[q]
        needy = sum(V[v][g] for g in X[v] if g != y[v]) <= p[v]
        C[('ka keeper needy', needy)] += 1
        # direct return
        X1 = [list(b) for b in X]; X1[v].remove(y[q]); X1[q].append(y[q])
        direct = VZ.efx0(V, X1)
        C[('direct return of Y_q is EFX0', direct)] += 1
        if direct: continue
        # which EFX0 constraints fail after the direct return
        viol = set()
        for i in range(n):
            vi = sum(V[i][g] for g in X1[i])
            for j in range(n):
                if i != j and any(sum(V[i][h] for h in X1[j] if h != g) > vi for g in X1[j]):
                    viol.add(('q' if i == q else 'v' if i == v else 'other') + ' envies ' + ('q' if j == q else 'v' if j == v else 'other'))
        C[('direct return fails by', tuple(sorted(viol)))] += 1
        # return + one junk move: which (from, to) roles work
        role = lambda a: 'q' if a == q else 'v' if a == v else 'other'
        works = set()
        for g in range(m):
            if g in picks: continue
            a = next(i for i in range(n) if g in X1[i])
            for b in range(n):
                if b == a: continue
                X2 = [list(t) for t in X1]; X2[a].remove(g); X2[b].append(g)
                if all(sum(V[i][h] for h in X2[i]) >= p[i] for i in range(n)) and VZ.efx0(V, X2): works.add(role(a) + '->' + role(b))
        C[('return + one junk move works', tuple(sorted(works)) if works else 'NONE')] += 1
for k in sorted(C, key=str): print(k, C[k])
