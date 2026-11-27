"""Lemma RF-A1* (k4/k3_oc1.md §13.6): oc1-hall's Lemma RF-A1 (k4/oc1_hall.md §24.6) with (A1-iv) weakened to
  (A1-iv*) every frozen agent q of Y' other than w, u, k2 that values Y_d has v_q(W) - min_W v_q <= p'_q,
W = {Y_d} + (J' - {h}).  Checks at every n = 5 DEMOTE-0 RF start with path u -> w -> d: Hall's (A1-i)..(A1-iii),
(A1-iv), (A1-iv*), the conclusion (raw EFX0 of X: w takes W, d takes {g, h}), and whether (A1-iv*) for the extra q
already follows from D_T' = empty (it does when q's two best goods of W are both junk).
    python3 k4/k3oc1/rf/rfa1_star.py RESIDUE.jsonl.gz"""
import sys, gzip, json, collections
from rf13_facts import efx0

def red(v, i, S):
    vs = [v[i].get(x, 0) for x in S]; return sum(vs) - min(vs)

C = collections.Counter()
for line in gzip.open(sys.argv[1], 'rt'):
    r = json.loads(line)
    if r['cls'] != 'DEMOTE-0' or len(r['path']) != 3: continue
    sets, vals, Y, Y2, path, u = r['sets'], r['vals'], r['Y'], r['Y2'], r['path'], r['u']
    n = len(sets); v = [dict(zip(sets[i], vals[i])) for i in range(n)]
    allg = set(x for s in sets for x in s); J = sorted(allg - set(Y)); J2 = sorted(allg - set(Y2))
    p = [v[i][Y[i]] for i in range(n)]; p2 = [v[i][Y2[i]] for i in range(n)]
    d, w = path[-1], path[1]; g = Y2[d]
    Jd = [x for x in J2 if x in v[d]]
    if not Jd: C['d values no good of J\' (A1 form undefined)'] += 1; continue
    h = max(Jd, key=lambda x: v[d][x]); W = [Y2[w]] + [x for x in J2 if x != h]
    X = [[Y2[i]] for i in range(n)]; X[w] = W; X[d] = [g, h]
    ok = efx0(v, X)
    frozenY = [i for i in range(n) if any(v[j].get(Y[i], 0) > p[j] for j in range(n) if j != i)]
    DTY = [i for i in frozenY if any(x in v[i] for x in J) and red(v, i, J) > p[i]]
    k2s = [k for k in DTY if k != d]
    A1i = d in DTY and sorted(x for x in J if x in v[d]) == sorted([g, h]) and Jd == [h]
    A1ii = sorted(x for x in W if x in v[u]) == sorted([Y[d], Y[u]]) and v[u][Y[d]] + v[u][Y[u]] < v[u][Y[w]]
    A1iii = len(k2s) == 1 and g in v[k2s[0]] and h in v[k2s[0]] and v[k2s[0]].get(Y[d], 0) <= p2[k2s[0]]
    frozen2 = [i for i in range(n) if any(v[j].get(Y2[i], 0) > p2[j] for j in range(n) if j != i)]
    qs = [i for i in frozen2 if i not in [w, u] + k2s and Y[d] in v[i]]
    A1iv = not qs
    A1ivs = all(red(v, q, W) <= p2[q] for q in qs)
    hyp = A1i and A1ii and A1iii and A1ivs
    C['hypotheses (A1-i..iii, iv*) %s, (A1-iv) %s, X EFX0 %s' % (hyp, A1iv, ok)] += 1
    if hyp and not ok: print('LEMMA VIOLATED', json.dumps(r), flush=True)
    for q in qs:
        best2 = sorted(W, key=lambda x: -v[q].get(x, 0))[:2]
        C['  extra q: its two best goods of W are both junk of Y\' (so (A1-iv*) follows from D_T\' = empty): %s' % (Y[d] not in best2)] += 1
for k in sorted(C): print(C[k], k)
