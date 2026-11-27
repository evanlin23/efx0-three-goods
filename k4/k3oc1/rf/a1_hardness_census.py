"""RF-A1*'s facts versus Y (k4/k3_oc1.md §13.7): on every n = 5 DEMOTE-0 RF start with path u -> w -> d (d taking a
junk good g of Y), the structure of the failing start Y: roles at Y (U, F, Dp, DT), the junk J, which agents value
which junk goods, the goods of d, u, w, and whether each fact (A1-i)..(A1-iii) holds.  Grouped into shapes up to the
values (the hypergraph, Y, Y', path, and the incidence of junk).
    python3 k4/k3oc1/rf/a1_hardness_census.py RESIDUE.jsonl.gz"""
import sys, gzip, json, collections
C = collections.Counter(); facts = collections.Counter()
def red(vs): return sum(vs) - min(vs)
for line in gzip.open(sys.argv[1], 'rt'):
    r = json.loads(line)
    if r['cls'] != 'DEMOTE-0' or len(r['path']) != 3: continue
    sets, vals, Y, Y2, path, u = r['sets'], r['vals'], r['Y'], r['Y2'], r['path'], r['u']
    n = len(sets); v = [dict(zip(sets[i], vals[i])) for i in range(n)]
    allg = set(x for s in sets for x in s); J = sorted(allg - set(Y)); J2 = sorted(allg - set(Y2))
    p = [v[i][Y[i]] for i in range(n)]; p2 = [v[i][Y2[i]] for i in range(n)]
    d, w = path[-1], path[1]; g = Y2[d]
    roles = []
    for i in range(n):
        fr = any(v[j].get(Y[i], 0) > p[j] for j in range(n) if j != i)
        if not fr: roles.append('U'); continue
        if not any(x in v[i] for x in J): roles.append('F'); continue
        vs = [v[i].get(x, 0) for x in J]
        roles.append('DT' if (sum(vs) > p[i] if 0 in vs else red(vs) > p[i]) else 'Dp')
    lab = {u: 'u', w: 'w', d: 'd'}
    who = tuple(sorted((x, tuple(sorted(lab.get(i, 'o%d' % i) for i in range(n) if x in v[i]))) for x in J))
    shape = (r['h'], tuple(Y), tuple(Y2), tuple(path), tuple(roles), 'junk valued by', who)
    C[shape] += 1
    Jd = [x for x in J2 if x in v[d]]
    h = max(Jd, key=lambda x: v[d][x]) if Jd else None
    A1i = h is not None and sorted(x for x in J if x in v[d]) == sorted([g, h]) and Jd == [h] and v[d][g] + v[d][h] > p[d]
    W = [Y[d]] + [x for x in J2 if x != h]
    A1ii = h is not None and sorted(x for x in W if x in v[u]) == sorted([Y[d], Y[u]]) and v[u][Y[d]] + v[u][Y[u]] < v[u][Y[w]]
    k2s = [k for k in range(n) if roles[k] == 'DT' and k != d]
    A1iii = h is not None and len(k2s) == 1 and g in v[k2s[0]] and h in v[k2s[0]] and v[k2s[0]].get(Y[d], 0) <= p2[k2s[0]]
    facts['(A1-i) %s (A1-ii) %s (A1-iii) %s' % (A1i, A1ii, A1iii)] += 1
for k, c in sorted(C.items(), key=lambda kv: -kv[1]): print(c, k)
for k in sorted(facts): print(facts[k], k)
