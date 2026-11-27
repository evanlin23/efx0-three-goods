"""Usage: census.py FILE.json.gz ...  (exports of OC1^max-failing starts; see k4/RFMIN.md §4 for where they are)
Census of OC1^max-failing starts: core features (K4.MC2, MC3, MC8, MC9 structures), receivers and whether a
receiver holds its top good (Lemma RF-TOP: then the receiver-first order has the same picks)."""
import sys, gzip, json, collections, itertools
import os; sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import twins_filter as TF

def kinds(sets):
    deg = collections.Counter(g for S in sets for g in S)
    out = []
    for S in sets:
        p = sum(deg[g] == 1 for g in S)
        out.append({(3, 1): 'P3', (3, 0): 'Q3', (4, 1): 'P4', (4, 0): 'Q4', (4, 2): 'PP4'}.get((len(S), p), '?%d%d' % (len(S), p)))
    return out, deg

for path in sys.argv[1:]:
    d = json.load(gzip.open(path))
    C = collections.Counter()
    for H in d['hypergraphs']:
        sets = H['sets']; kd, deg = kinds(sets); n = len(sets)
        feats = []
        if 'PP4' in kd: feats.append('PP4 (not MC2)')
        if any(deg[g] == 2 and all(kd[i] == 'P3' for i in range(n) if g in sets[i]) for g in deg): feats.append('P3-P3 deg-2 good (not MC3)')
        if TF.excluded(sets): feats.append('certified double edge (not MC8)')
        if TF.has_claw(sets): feats.append('claw (not MC9)')
        fs = ', '.join(feats) or 'in the K4.MC2/3/8/9 structural class'
        C['hypergraph: ' + fs] += 1
        for s in H['starts']:
            v = [dict(zip(S, vals)) for S, vals in zip(sets, s['vals'])]
            Y = s['picks']
            rec = [u for u in range(n) if Y[u] is not None and all(v[i].get(Y[u], 0) <= v[i].get(Y[i], 0) for i in range(n) if i != u)]
            assert sorted(rec) == sorted(s['receivers']), (rec, s['receivers'])
            C['starts'] += 1
            for u in rec:
                top = max(v[u], key=v[u].get)
                C['receiver kind %s' % kd[u]] += 1
                C['receiver holds its top' if Y[u] == top else 'receiver does not hold its top'] += 1
                C['receiver pick private' if deg[Y[u]] == 1 else 'receiver pick shared (deg %d)' % deg[Y[u]]] += 1
            C['starts in structural class' if not feats else 'starts outside'] += 1
    print(path)
    for k, x in sorted(C.items()): print('   %-60s %d' % (k, x))
