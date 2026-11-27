"""Lemma NA on every n = 5 DEMOTE-0 RF start (k4/k3_oc1.md §13.5): does a no-absorber completion (every junk good of
J' to a different agent, criterion of Lemma NA) exist?  Counted by whether the start also completes by RF-A1*'s form.
    python3 k4/k3oc1/rf/demote0_na_all.py RESIDUE.jsonl.gz"""
import sys, gzip, json, itertools, collections
from rf13_facts import efx0
C = collections.Counter()
for line in gzip.open(sys.argv[1], 'rt'):
    r = json.loads(line)
    if r['cls'] != 'DEMOTE-0': continue
    sets, vals, Y2, path = r['sets'], r['vals'], r['Y2'], r['path']
    n = len(sets); v = [dict(zip(sets[i], vals[i])) for i in range(n)]
    allg = set(x for s in sets for x in s); J2 = sorted(allg - set(Y2))
    d = path[-1]; w = path[1] if len(path) > 1 else d
    Jd = [x for x in J2 if x in v[d]]; a1 = False
    if w != d and Jd:
        h = max(Jd, key=lambda x: v[d][x]); X = [[g] for g in Y2]; X[w] += [x for x in J2 if x != h]; X[d].append(h); a1 = efx0(v, X)
    na = False
    for asg in itertools.permutations(range(n), len(J2)):
        X = [[g] for g in Y2]
        for x, a in zip(J2, asg): X[a].append(x)
        if efx0(v, X): na = True; break
    C['%s: RF-A1* form %s, no-absorber completion %s' % (r['h'], a1, na)] += 1
for k in sorted(C): print(C[k], k)
