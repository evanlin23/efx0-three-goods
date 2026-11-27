"""Lemma UNTANGLE (kgen/rounds.md §4.13): failure counts of explicit rules for the swap's junk good h, at every
non-witness MD EFX0 allocation of random strict cores (all have a needy keep-and-add pair q, v).  The move: (U0) return
Y_q to q if that is EFX0; otherwise (U1) also move the rule's h from X_q to v.  Rules:
  envied     h maximises max_{i != q} v_i(h)             (the junk good some other agent values most)
  violator   h maximises max over the agents violating EFX0 after the return of v_i(h) (falls back to 'envied')
  envysum    h maximises sum_{i != q} v_i(h) / p_i
  keeper     h maximises v_v(h)                         (the keeper's favourite)
  violmin    h maximises min over the violators of v_i(h)
  fixq       h maximises the number of agents with no EFX0 violation toward q's new bundle (then 'violator')
  qleast     h minimises v_q(h)                         (q's least valued)
  any        some h works (the benchmark: the best single swap)
    python3 kgen/rounds/untangle_rule.py n,m,count,seed"""
import sys, os, json, collections, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import rndlib, recs_vs_rndp as RV, verify_k4zero as VZ
from splice_search import rows_of, dense

RULES = ['envied', 'violator', 'violmin', 'fixq', 'envysum', 'keeper', 'qleast', 'any']


def violators(V, X):
    n = len(V); out = set()
    for i in range(n):
        vi = sum(V[i][g] for g in X[i])
        for j in range(n):
            if i != j and any(sum(V[i][h] for h in X[j] if h != g) > vi for g in X[j]): out.add(i)
    return out


def ok(V, X, p):
    return all(sum(V[i][g] for g in X[i]) >= p[i] for i in range(len(V))) and VZ.efx0(V, X)


C = collections.Counter(); fails = collections.defaultdict(list); t0 = time.time()
for row in rows_of('random', sys.argv[1], 1):
    V = dense(row['sets'], row['vals']); n, m = len(V), len(V[0]); y = tuple(row['picks']); p = [V[a][y[a]] for a in range(n)]; picks = set(y)
    alls, _ = rndlib.list_efx(V)
    for o in alls:
        X = [[g for g in range(m) if o[g] == i] for i in range(n)]
        if any(sum(V[a][g] for g in X[a]) < p[a] for a in range(n)) or RV.structures(V, y, X, False): continue
        f = [o[y[a]] for a in range(n)]
        qs = [a for a in range(n) if not any(g in picks for g in X[a]) and f[a] != a and f[f[a]] == f[a]]
        if not qs: C['non-witness without a keep-and-add pair'] += 1; continue
        q = qs[0]; v = f[q]; C['non-witnesses'] += 1
        X0 = [list(b) for b in X]; X0[v].remove(y[q]); X0[q].append(y[q])
        if ok(V, X0, p): C['U0 return works'] += 1; continue
        junk = [h for h in X[q]]
        viol = violators(V, X0) - {q}
        def fixed_toward_q(h):   # how many agents i != q have no EFX0 violation toward q's bundle X_q - h + Y_q
            B = [g for g in X0[q] if g != h]; cnt = 0
            for i in range(n):
                if i == q: continue
                Bi = B; Xi = X0[i] + ([h] if i == v else [])
                vi = sum(V[i][g] for g in Xi)
                if not any(sum(V[i][t] for t in Bi if t != g) > vi for g in Bi): cnt += 1
            return cnt
        def swap(h):
            X1 = [list(b) for b in X0]; X1[q].remove(h); X1[v].append(h); return ok(V, X1, p)
        choice = {
            'envied': max(junk, key=lambda h: (max(V[i][h] for i in range(n) if i != q), -h)),
            'violator': max(junk, key=lambda h: ((max(V[i][h] for i in viol) if viol else 0), max(V[i][h] for i in range(n) if i != q), -h)),
            'envysum': max(junk, key=lambda h: (sum(V[i][h] / p[i] for i in range(n) if i != q), -h)),
            'keeper': max(junk, key=lambda h: (V[v][h], -h)),
            'violmin': max(junk, key=lambda h: ((min(V[i][h] for i in viol) if viol else 0), max(V[i][h] for i in range(n) if i != q), -h)),
            'fixq': max(junk, key=lambda h: (fixed_toward_q(h), (max(V[i][h] for i in viol) if viol else 0), -h)),
            'qleast': min(junk, key=lambda h: (V[q][h], h)),
        }
        anyok = any(swap(h) for h in junk)
        for r in RULES:
            good = anyok if r == 'any' else swap(choice[r])
            C[(r, 'U0 or rule swap works' if good else 'FAILS')] += 1
            if not good and r != 'any' and len(fails[r]) < 2:
                fails[r].append({'V': V, 'picks': y, 'X': X, 'q': q, 'v': v, 'h': choice[r], 'some h works': anyok})
for k in sorted(C, key=str): print(k, C[k])
for r, v in fails.items():
    for e in v: print('FAILURE', r, json.dumps(e))
print('time %.0f s' % (time.time() - t0))
