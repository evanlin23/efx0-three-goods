"""Dictionary k = 3 -> k = 4 at RF starts (k4/k3_oc1.md §13).  DEMOTE-0's trade 'p takes {Y'_d, j}, d takes Y'_p'
is, in k = 3 terms, the ring d -> p -> d with one pair arrow: p is exposed for owner d (p's lower goods {Y'_d, j} lie
in J' + base(d)).  At k = 3 an exposed agent holds its top.  Census on girth's build: for every valid trade (p
pick-dangerous at Y', j in J', both improve), p's rank at Y', and whether {Y'_d, j} are p's two goods just below
its pick; for (1, 3) the same for w and H.
    python3 k4/k3oc1/rf/rf_dict.py RESIDUE.jsonl.gz"""
import sys, gzip, json, itertools, collections
C = collections.Counter()
for line in gzip.open(sys.argv[1], 'rt'):
    r = json.loads(line)
    sets, vals, Y2, path = r['sets'], r['vals'], r['Y2'], r['path']
    n = len(sets); v = [dict(zip(sets[i], vals[i])) for i in range(n)]
    allg = set(g for s in sets for g in s); J2 = sorted(allg - set(Y2)); p2 = [v[i][Y2[i]] for i in range(n)]
    order = [sorted(sets[i], key=lambda g: -v[i][g]) for i in range(n)]
    d = path[-1]
    if r['cls'] == 'DEMOTE-0':
        ranks = set()
        for p in range(n):
            if p == d: continue
            for j in J2:
                if j not in v[p] or Y2[d] not in v[p]: continue
                if v[p][Y2[d]] + v[p][j] > p2[p] and v[d].get(Y2[p], 0) > p2[d]:
                    ranks.add((order[p].index(Y2[p]), tuple(sorted(order[p].index(g) for g in (Y2[d], j)))))
        C['DEMOTE-0: valid trades (p rank at Y\', ranks of Y\'_d and j in p\'s order): %s' % sorted(ranks)] += 1
    else:
        w = path[1]
        H = [H for H in itertools.combinations(J2, 2) if sum(v[w].get(g, 0) for g in H) > p2[w]][0]
        C['(1, 3): w rank at Y\' %d, ranks of H in w\'s order %s' % (order[w].index(Y2[w]), sorted(order[w].index(g) for g in H))] += 1
for k in sorted(C): print(C[k], k)
