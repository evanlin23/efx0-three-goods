"""RF-A1 at n = 5 (k4/k3_oc1.md §13.6): DEMOTE-0 RF starts (one receiver d, no truly dangerous agent at Y') that
complete by oc1-hall's A1 form: w takes W = {Y'_w} + (J' - {h}), d takes {Y'_d, h}, h = d's favourite good of J'
(k4/oc1_hall.md §24.6; girth's census: all 71,443 at-once DEMOTE-0 starts at n = 5).  Census of the facts:
  - path length; h = Y_u?;  J' n R_d = {h}?;  d threatened at Y by {g, h} (v_d(g) + v_d(h) > v_d(Y_d))?;
  - Hall's (A1-i)..(A1-iv) as stated (d truly dangerous at Y with junk pair {g, h}; u values exactly Y_d, Y_u of W
    with v_u(Y_d) + v_u(Y_u) < v_u(Y_w); the other truly dangerous agent k2 of Y values g, h and does not want Y_d;
    no frozen agent of Y' other than w, u, k2 values Y_d);
  - the reduction's two conditions: (A) d: v_d(W) - min_W v_d <= v_d(g) + v_d(h); (B) every i outside {w, d} that
    values Y'_w: v_i(W) - min_W v_i <= p'_i;  and raw EFX0 of X.
    python3 k4/k3oc1/rf/rfa1_n5.py RESIDUE.jsonl.gz"""
import sys, gzip, json, collections
from rf13_facts import efx0

def red(v, i, S):
    vs = [v[i].get(g, 0) for g in S]; return sum(vs) - min(vs)

C = collections.Counter()
for line in gzip.open(sys.argv[1], 'rt'):
    r = json.loads(line)
    if r['cls'] != 'DEMOTE-0': continue
    sets, vals, Y, Y2, path, u = r['sets'], r['vals'], r['Y'], r['Y2'], r['path'], r['u']
    n = len(sets); v = [dict(zip(sets[i], vals[i])) for i in range(n)]
    allg = set(g for s in sets for g in s); J = sorted(allg - set(Y)); J2 = sorted(allg - set(Y2))
    p = [v[i][Y[i]] for i in range(n)]; p2 = [v[i][Y2[i]] for i in range(n)]
    d = path[-1]; w = path[1] if len(path) > 1 else d
    if w == d: C['path length 1 (w = d): A1 form undefined'] += 1; continue
    Jd = [g for g in J2 if g in v[d]]
    if not Jd: C['d values no good of J\''] += 1; continue
    h = max(Jd, key=lambda g: v[d][g]); g = Y2[d]
    W = [Y2[w]] + [x for x in J2 if x != h]
    X = [[Y2[i]] for i in range(n)]; X[w] = W; X[d] = [g, h]
    ok = efx0(v, X)
    if not ok: continue
    tag = 'A1 at-once, path length %d: ' % (len(path) - 1)
    C[tag + 'starts'] += 1
    C[tag + 'g is junk of Y %s' % (g in J)] += 1
    C[tag + 'h = Y_u %s' % (h == Y[u])] += 1
    C[tag + "J' n R_d = {h} %s" % (Jd == [h])] += 1
    C[tag + 'd threatened at Y by {g, h}: %s' % (v[d].get(g, 0) + v[d][h] > p[d])] += 1
    # roles at Y
    frozenY = [i for i in range(n) if any(v[j].get(Y[i], 0) > p[j] for j in range(n) if j != i)]
    DTY = [i for i in frozenY if any(x in v[i] for x in J) and red(v, i, J) > p[i]]
    C[tag + '|D_T(Y)| = %d' % len(DTY)] += 1
    A1i = d in DTY and sorted(x for x in J if x in v[d]) == sorted([g, h]) and Jd == [h]
    WuV = sorted(x for x in W if x in v[u])
    A1ii = WuV == sorted([Y[d], Y[u]]) and v[u][Y[d]] + v[u][Y[u]] < v[u][Y[w]]
    k2s = [k for k in DTY if k != d]
    A1iii = len(k2s) == 1 and g in v[k2s[0]] and h in v[k2s[0]] and v[k2s[0]].get(Y[d], 0) <= p2[k2s[0]]
    frozen2 = [i for i in range(n) if any(v[j].get(Y2[i], 0) > p2[j] for j in range(n) if j != i)]
    A1iv = all(Y[d] not in v[i] for i in frozen2 if i not in [w, u] + k2s)
    C[tag + 'Hall facts (A1-i) %s (A1-ii) %s (A1-iii) %s (A1-iv) %s' % (A1i, A1ii, A1iii, A1iv)] += 1
    A = red(v, d, W) <= v[d].get(g, 0) + v[d][h]
    B = all(red(v, i, W) <= p2[i] for i in range(n) if i not in (w, d) and Y2[w] in v[i])
    C[tag + 'reduction (A) %s (B) %s' % (A, B)] += 1
    valuers = sorted(('u' if i == u else 'frozen' if i in frozen2 else 'unfrozen') for i in range(n) if i not in (w, d) and Y2[w] in v[i])
    C[tag + "agents outside w, d valuing Y'_w = Y_d: %s" % valuers] += 1
for k in sorted(C): print(C[k], k)
