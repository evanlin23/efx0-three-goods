"""RF class (1, 3): for girth's form X (w takes H + {y}, d takes {Y'_w, Y'_d, x}; H the unique improving pair that
works), which agents do the two multi-good bundles W = H + {y} and Z = {Y'_w, Y'_d, x} threaten, for each choice of
(x, y); and the structural facts a lemma can use.
    python3 k4/k3oc1/rf/rf13_threats.py RESIDUE.jsonl.gz"""
import sys, gzip, json, itertools, collections
from rf13_facts import efx0, threat

def thr(v, i, S, val):
    vs = [v[i].get(g, 0) for g in S]
    return sum(vs) - min(vs) > val

C = collections.Counter(); shown = 0
for line in gzip.open(sys.argv[1], 'rt'):
    r = json.loads(line)
    if r['cls'] != '(1, 3)': continue
    sets, vals, Y, Y2, path = r['sets'], r['vals'], r['Y'], r['Y2'], r['path']
    n = len(sets); v = [dict(zip(sets[i], vals[i])) for i in range(n)]
    allg = sorted(set(g for s in sets for g in s)); J2 = [g for g in allg if g not in Y2]
    p2 = [v[i][Y2[i]] for i in range(n)]
    u, w, d = path[0], path[1], path[-1]
    others = [i for i in range(n) if i not in (u, w, d)]
    Hs = [H for H in itertools.combinations(J2, 2) if sum(v[w].get(g, 0) for g in H) > p2[w]]
    C['improving pairs for w: %d' % len(Hs)] += 1
    for H in Hs:
        rest = [g for g in J2 if g not in H]
        for x in rest:
            y = [g for g in rest if g != x][0]
            X = [[Y2[i]] for i in range(n)]; X[w] = list(H) + [y]; X[d] = [Y2[w], Y2[d], x]; X[u] = [Y2[u]]
            val = [sum(v[i].get(g, 0) for g in X[i]) for i in range(n)]
            tW = [i for i in range(n) if i != w and thr(v, i, X[w], val[i])]
            tZ = [i for i in range(n) if i != d and thr(v, i, X[d], val[i])]
            ok = efx0(v, X)
            role = lambda i: 'u' if i == u else 'w' if i == w else 'd' if i == d else 'other'
            C['H improving; x=%s: EFX0 %s; W threatens %s; Z threatens %s' % ('d-fav' if x == max(rest, key=lambda g: v[d].get(g, 0)) else 'd-nonfav',
              ok, sorted(role(i) for i in tW), sorted(role(i) for i in tZ))] += 1
for k in sorted(C): print(C[k], k)
