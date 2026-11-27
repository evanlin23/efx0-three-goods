"""At the DEMOTE-0 RF starts where the A1 completion fails (girth's (i) holds exactly by
the A1 form, k4/girth.md §7), the trades 'p takes {Y'_d, j}, d takes Y'_p' that leave a completion where every
remaining junk good goes to a different agent (girth's explicit form), and the rank of p's pick at Y' for those.
A rank-1 p taking its two lowest goods is a (DE-a) move, impossible at k = 3.
    python3 k4/k3oc1/rf/rf_dea_moves.py RESIDUE.jsonl.gz"""
import sys, gzip, json, itertools, collections
from rf13_facts import efx0
C = collections.Counter()
for line in gzip.open(sys.argv[1], 'rt'):
    r = json.loads(line)
    if r['cls'] != 'DEMOTE-0': continue
    sets, vals, Y2, path = r['sets'], r['vals'], r['Y2'], r['path']
    n = len(sets); v = [dict(zip(sets[i], vals[i])) for i in range(n)]
    allg = set(g for s in sets for g in s); J2 = sorted(allg - set(Y2)); p2 = [v[i][Y2[i]] for i in range(n)]
    order = [sorted(sets[i], key=lambda g: -v[i][g]) for i in range(n)]
    d = path[-1]; w = path[1] if len(path) > 1 else d
    Jd = [g for g in J2 if g in v[d]]
    a1 = False
    if w != d and Jd:
        h = max(Jd, key=lambda g: v[d][g]); X = [[g] for g in Y2]; X[w] += [g for g in J2 if g != h]; X[d].append(h); a1 = efx0(v, X)
    if a1: C['A1 completes at the picks'] += 1; continue
    good = set()
    for p in range(n):
        if p == d: continue
        for j in J2:
            if j not in v[p] or Y2[d] not in v[p]: continue
            if not (v[p][Y2[d]] + v[p][j] > p2[p] and v[d].get(Y2[p], 0) > p2[d]): continue
            rest = [g for g in J2 if g != j]
            for asg in itertools.permutations(range(n), len(rest)):   # every remaining junk good to a different agent
                X = [[g] for g in Y2]; X[p] = [Y2[d], j]; X[d] = [Y2[p]]
                for g, a in zip(rest, asg): X[a].append(g)
                if efx0(v, X): good.add(order[p].index(Y2[p])); break
    C['A1 form fails (the picks may still complete with another owner); ranks of p over trades after which every junk good goes to a different agent: %s' % sorted(good)] += 1
for k in sorted(C): print(C[k], k)
