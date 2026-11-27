"""Lemma NA (k4/k3_oc1.md §13.5): the no-absorber completions of DEMOTE-0 RF starts at n = 5 that are not RF-A1*.
X gives each junk good of J' to a different agent.  Every bundle then has at most two goods, so X is EFX0 iff every
wanter i of a receiving agent a's pick is compensated: v_i(X_i) >= v_i(Y'_a).  Census of the receivers, of the
compensation needed, and a check of the equivalence against raw EFX0.
    python3 k4/k3oc1/rf/demote0_na.py RESIDUE.jsonl.gz"""
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
    found = []
    for asg in itertools.permutations(range(n), len(J2)):
        X = [[g] for g in Y2]
        for x, a in zip(J2, asg): X[a].append(x)
        val = [sum(v[i].get(x, 0) for x in X[i]) for i in range(n)]
        crit = all(v[i].get(Y2[a], 0) <= val[i] for a in asg for i in range(n) if i != a)
        ok = efx0(v, X)
        C['criterion agrees with raw EFX0: %s' % (crit == ok)] += 1
        if ok: found.append(asg)
    if not found: C['no no-absorber completion'] += 1; continue
    def role(i): return 'u' if i == u else 'w' if i == w else 'd' if i == d else 'off'
    # the compensations used in the first completion
    asg = found[0]; X = [[g] for g in Y2]
    for x, a in zip(J2, asg): X[a].append(x)
    val = [sum(v[i].get(x, 0) for x in X[i]) for i in range(n)]
    comp = sorted('%s wants %s\'s pick, compensated' % (role(i), role(a)) for a in asg for i in range(n) if i != a and v[i].get(Y2[a], 0) > p2[i])
    C['receivers %s; compensations %s; d takes its favourite junk %s' % (sorted(role(a) for a in asg), comp,
      X[d][-1] == max(Jd, key=lambda x: v[d][x]) if Jd else None)] += 1
for k, c in sorted(C.items(), key=lambda kv: -kv[1]): print(c, k)
