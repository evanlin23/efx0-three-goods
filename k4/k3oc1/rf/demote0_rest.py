"""DEMOTE-0 at n = 5: the starts that complete at the picks but not by the A1 form (RF-A1*).  Every one-absorber
completion there, classified by who absorbs (role on the RF path: u, w, d, or an off-path agent, and that agent's
role at Y') and where the other junk goods go; the hypergraph; the path length.
    python3 k4/k3oc1/rf/demote0_rest.py RESIDUE.jsonl.gz"""
import sys, gzip, json, itertools, collections
from rf13_facts import efx0
C = collections.Counter()
for line in gzip.open(sys.argv[1], 'rt'):
    r = json.loads(line)
    if r['cls'] != 'DEMOTE-0': continue
    sets, vals, Y, Y2, path, u = r['sets'], r['vals'], r['Y'], r['Y2'], r['path'], r['u']
    n = len(sets); v = [dict(zip(sets[i], vals[i])) for i in range(n)]
    allg = set(x for s in sets for x in s); J2 = sorted(allg - set(Y2)); p2 = [v[i][Y2[i]] for i in range(n)]
    d = path[-1]; w = path[1] if len(path) > 1 else d
    Jd = [x for x in J2 if x in v[d]]
    if w != d and Jd:
        h = max(Jd, key=lambda x: v[d][x]); X = [[g] for g in Y2]; X[w] += [x for x in J2 if x != h]; X[d].append(h)
        if efx0(v, X): continue
    frozen = [i for i in range(n) if any(v[j].get(Y2[i], 0) > p2[j] for j in range(n) if j != i)]
    def role(i):
        return 'u' if i == u else 'w' if i == w else 'd' if i == d else ('off-path ' + ('Dp' if any(x in v[i] for x in J2) else 'F') if i in frozen else 'off-path U')
    forms = set()
    for asg in itertools.product(range(n), repeat=len(J2)):
        ab = [a for a in range(n) if asg.count(a) >= 2]
        if len(ab) > 1: continue
        X = [[g] for g in Y2]
        for x, a in zip(J2, asg): X[a].append(x)
        if efx0(v, X):
            singles = tuple(sorted(role(a) for a in set(asg) if asg.count(a) == 1))
            forms.add((role(ab[0]) if ab else 'none', singles))
    C['%s path %d: completes at picks %s; forms %s' % (r['h'], len(path) - 1, bool(forms), sorted(forms)[:4])] += 1
for k, c in sorted(C.items(), key=lambda kv: -kv[1]): print(c, k)
