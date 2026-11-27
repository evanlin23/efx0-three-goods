"""Lemma UNTANGLE's second kind of move (kgen/rounds.md §4.13).  At every non-witness MD EFX0 allocation of random
strict cores (a needy keep-and-add pair q, v), after the return (U0) of Y_q to q:
  U1   one junk good of X_q moves to v (best h);
  U1'  one junk good of X_q moves to another agent;
  U3   one junk good moves INTO v from a bundle that v envies after the return ((O2): the referee's block, where the
       envied bundle holds an earlier agent's pick that v values above p_v); U3r: the rule 'v's favourite junk good of
       the envied bundles';
  U13  one junk good of X_q leaves q AND one junk good enters v from another bundle (two junk moves);
  U2   none of these: some other MD EFX0 allocation with larger Φ.
    python3 kgen/rounds/untangle_u3.py n,m,count,seed"""
import sys, os, json, collections, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import rndlib, recs_vs_rndp as RV, verify_k4zero as VZ
from splice_search import rows_of, dense


def ok(V, X, p): return all(sum(V[i][g] for g in X[i]) >= p[i] for i in range(len(V))) and VZ.efx0(V, X)


def envied_by(V, X, i):
    vi = sum(V[i][g] for g in X[i])
    return [j for j in range(len(V)) if j != i and any(sum(V[i][h] for h in X[j] if h != g) > vi for g in X[j])]


def move(X, g, a, b):
    Y = [list(t) for t in X]; Y[a].remove(g); Y[b].append(g); return Y


C = collections.Counter(); ex = []
for row in rows_of('random', sys.argv[1], 1):
    V = dense(row['sets'], row['vals']); n, m = len(V), len(V[0]); y = tuple(row['picks']); p = [V[a][y[a]] for a in range(n)]; picks = set(y)
    alls, _ = rndlib.list_efx(V)
    for o in alls:
        X = [[g for g in range(m) if o[g] == i] for i in range(n)]
        if any(sum(V[a][g] for g in X[a]) < p[a] for a in range(n)) or RV.structures(V, y, X, False): continue
        f = [o[y[a]] for a in range(n)]
        qs = [a for a in range(n) if not any(g in picks for g in X[a]) and f[a] != a and f[f[a]] == f[a]]
        if not qs: continue
        q = qs[0]; v = f[q]; C['non-witnesses'] += 1
        X0 = move(X, y[q], v, q)
        if ok(V, X0, p): C['U0'] += 1; continue
        if any(ok(V, move(X0, h, q, v), p) for h in X0[q] if h not in picks): C['U1'] += 1; continue
        if any(ok(V, move(X0, h, q, w), p) for h in X0[q] if h not in picks for w in range(n) if w not in (q, v)): C["U1'"] += 1; continue
        env = envied_by(V, X0, v)
        cand = [(g, j) for j in env for g in X0[j] if g not in picks]
        if cand:
            g, j = max(cand, key=lambda t: (V[v][t[0]], -t[0]))
            if ok(V, move(X0, g, j, v), p): C['U3r (rule: v\'s favourite junk of an envied bundle)'] += 1; continue
        if any(ok(V, move(X0, g, j, v), p) for j in range(n) if j != v for g in X0[j] if g not in picks): C['U3 (some junk into v)'] += 1; continue
        two = False
        for h in [h for h in X0[q] if h not in picks]:
            for w in range(n):
                if w == q: continue
                X1 = move(X0, h, q, w)
                if any(ok(V, move(X1, g, j, v), p) for j in range(n) if j != v for g in X1[j] if g not in picks and (j, g) != (w, h)): two = True; break
            if two: break
        if two: C['U13 (two junk moves)'] += 1; continue
        C['U2 needed'] += 1
        if len(ex) < 3: ex.append({'V': V, 'picks': y, 'X': X, 'q': q, 'v': v, 'O2 envied after return': env})
for k in sorted(C, key=str): print(k, C[k])
for e in ex: print('U2 NEEDED', json.dumps(e))
