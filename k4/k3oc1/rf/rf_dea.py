"""Does receiver-first restore the k = 3 fact (DE-a)?  At k = 3 only an agent holding its top good can be threatened
by a bundle of junk.  On the RF starts of girth's build (classes DEMOTE-0 and (1, 3) at n = 5): is every agent that
some set of junk goods threatens (at its pick value) a top-holder?  And in the repairing move of each class, does a
non-top-holder take junk (the (DE-a) move)?
    python3 k4/k3oc1/rf/rf_dea.py RESIDUE.jsonl.gz"""
import sys, gzip, json, itertools, collections
C = collections.Counter()
for line in gzip.open(sys.argv[1], 'rt'):
    r = json.loads(line)
    sets, vals, Y2, path = r['sets'], r['vals'], r['Y2'], r['path']
    n = len(sets); v = [dict(zip(sets[i], vals[i])) for i in range(n)]
    allg = set(g for s in sets for g in s); J2 = sorted(allg - set(Y2)); p2 = [v[i][Y2[i]] for i in range(n)]
    top = [max(sets[i], key=lambda g: v[i][g]) for i in range(n)]
    def threatened(i):   # some junk set S, |S| >= 2, with v(S) - min v(S) > p_i
        vs = sorted((v[i].get(g, 0) for g in J2), reverse=True)
        return len(vs) >= 2 and vs[0] + vs[1] > p2[i]
    thr = [i for i in range(n) if threatened(i)]
    nontop = [i for i in thr if Y2[i] != top[i]]
    rank = lambda i: sorted(sets[i], key=lambda g: -v[i][g]).index(Y2[i])
    C['%s: some junk-threatened agent holds less than its top: %s' % (r['cls'], bool(nontop))] += 1
    for i in nontop: C['%s:   junk-threatened non-top-holder holds its rank-%d good' % (r['cls'], rank(i))] += 1
    if r['cls'] == '(1, 3)':
        w = path[1]; C['(1, 3): w (which takes the junk pair) holds its rank-%d good at Y\'' % rank(w)] += 1
for k in sorted(C): print(C[k], k)
