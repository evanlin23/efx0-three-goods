"""RF-A1 at n = 5: replacement for Hall's (A1-iv).  At the A1 at-once DEMOTE-0 starts where (A1-iv) fails, the extra
frozen agents q (not w, u, k2, d) that value Y_d: do they value any other good of W = {Y_d} + (J' - {h}), and do they
want Y_d at Y'?  Candidate (A1-iv'): every frozen agent of Y' other than w, u, k2 that values Y_d values no good of
J' - {h} and has v_q(Y_d) <= p'_q.
    python3 k4/k3oc1/rf/rfa1_iv.py RESIDUE.jsonl.gz"""
import sys, gzip, json, collections
from rf13_facts import efx0
C = collections.Counter()
for line in gzip.open(sys.argv[1], 'rt'):
    r = json.loads(line)
    if r['cls'] != 'DEMOTE-0' or len(r['path']) != 3: continue
    sets, vals, Y, Y2, path, u = r['sets'], r['vals'], r['Y'], r['Y2'], r['path'], r['u']
    n = len(sets); v = [dict(zip(sets[i], vals[i])) for i in range(n)]
    allg = set(g for s in sets for g in s); J = sorted(allg - set(Y)); J2 = sorted(allg - set(Y2))
    p = [v[i][Y[i]] for i in range(n)]; p2 = [v[i][Y2[i]] for i in range(n)]
    d, w = path[-1], path[1]
    Jd = [x for x in J2 if x in v[d]]
    if not Jd: continue
    h = max(Jd, key=lambda x: v[d][x]); g = Y2[d]; W = [Y2[w]] + [x for x in J2 if x != h]
    X = [[Y2[i]] for i in range(n)]; X[w] = W; X[d] = [g, h]
    if not efx0(v, X): continue
    frozenY = [i for i in range(n) if any(v[j].get(Y[i], 0) > p[j] for j in range(n) if j != i)]
    DTY = [i for i in frozenY if (lambda vs: sum(vs) - min(vs))([v[i].get(x, 0) for x in J]) > p[i] and any(x in v[i] for x in J)]
    k2 = [k for k in DTY if k != d][0]
    frozen2 = [i for i in range(n) if any(v[j].get(Y2[i], 0) > p2[j] for j in range(n) if j != i)]
    qs = [i for i in frozen2 if i not in (w, u, k2, d) and Y[d] in v[i]]
    if not qs: C['(A1-iv) holds'] += 1; continue
    for q in qs:
        other = [x for x in W if x != Y[d] and x in v[q]]
        C['q: values other goods of W: %s; wants Y_d at Y\': %s; holds its top at Y\': %s; role at Y: %s' % (
            bool(other), v[q][Y[d]] > p2[q], Y2[q] == max(sets[q], key=lambda x: v[q][x]),
            'D_T' if q in DTY else 'frozen' if q in frozenY else 'unfrozen')] += 1
    iv2 = all(not [x for x in W if x != Y[d] and x in v[q]] and v[q][Y[d]] <= p2[q] for q in qs)
    C["(A1-iv') holds %s" % iv2] += 1
for k in sorted(C): print(C[k], k)
