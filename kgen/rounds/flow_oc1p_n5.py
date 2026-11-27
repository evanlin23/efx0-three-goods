"""Mechanism of the certifier's n = 5 OC1'^max counterexamples (kgen/rounds.md §4.8): for each, one round of disjoint
chains (verify_k4zero.brute: free and one absorber), OC2-like two rounds if one fails, and the pick flow of every MD EFX0
allocation (the permutation part: who holds whose pick; agents that lost their pick).
    python3 kgen/rounds/flow_oc1p_n5.py [N]"""
import sys, os, json, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import rndlib, verify_k4zero as VZ
N = int(sys.argv[1]) if len(sys.argv) > 1 else 99
R = os.path.join(HERE, '..', '..', 'results', 'kgen_rounds')
C = collections.Counter()
for t, line in enumerate(open(os.path.join(R, 'certifier_oc1prime_cex_n5.jsonl'))):
    if t >= N: break
    x = json.loads(line); sets = x['sets']; m = 1 + max(max(s) for s in sets); n = len(sets)
    V = [[0] * m for _ in sets]
    for i, (s, vv) in enumerate(zip(sets, x['vals'])):
        for g, v in zip(s, vv): V[i][g] = v
    res, _ = rndlib.oc1z(V); r = next(r for r in res if list(r['picks']) == x['picks'])
    b = VZ.brute(V, r['order'])
    y = x['picks']; flows = collections.Counter()
    L, _ = rndlib.list_efx(V)
    for own in L:
        X = [[g for g in range(m) if own[g] == i] for i in range(n)]
        if not all(VZ.val(V, i, X[i]) >= V[i][y[i]] for i in range(n)): continue
        loc = [own[y[a]] for a in range(n)]
        # cycles / paths of the map a -> loc(a) on movers
        mv = [a for a in range(n) if loc[a] != a]
        comps = []; seen = set()
        for a in mv:
            if a in seen: continue
            c = [a]; seen.add(a); z = loc[a]
            while z != a and z not in seen and loc[z] != z: c.append(z); seen.add(z); z = loc[z]
            comps.append(tuple(c) + (('cycle',) if z == a else ('into %d' % z,)))
        flows[tuple(sorted(comps))] += 1
    C[('one round', b['round_1'])] += 1
    print('%2d idx %s order %s | one round (1 absorber) %s, free %s | MD pick flows: %s' % (t, x['idx'], r['order'], b['round_1'], b['round_free'], dict(flows)), flush=True)
print(dict(C))
