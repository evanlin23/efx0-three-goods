"""Compare this workstream's OC1^max counterexamples with the certifier's 11 (results/k4_oc1max/oc1max_cex_n4.json on
branch compute/k4-oc1max-cert, copied to results/kgen_rounds/certifier_oc1max_cex_n4.json): is every strict-core
hypergraph of zcore_fails.json (and C4K) isomorphic to one of the 11?  Then, on the 11: the starved-agent certificate at
every failing perfect start (zero-aware), OC1' (rnd.c and the forward brute force) and two rounds (brute force).
    python3 kgen/rounds/vs_certifier.py"""
import sys, os, json
import networkx as nx
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import rndlib, verify_k4zero as VZ, c4k_core, itertools
R = os.path.join(HERE, '..', '..', 'results', 'kgen_rounds')
cert = json.load(open(os.path.join(R, 'certifier_oc1max_cex_n4.json')))['instances']
mine = json.load(open(os.path.join(R, 'zcore_fails.json')))


def G(sets):
    g = nx.Graph()
    for i, s in enumerate(sets):
        g.add_node(('a', i), t='a')
        for x in s: g.add_node(('g', x), t='g'); g.add_edge(('a', i), ('g', x))
    return g


nm = lambda a, b: a['t'] == b['t']
CG = [G(c['sets']) for c in cert]
print('certifier instances:', len(cert))
for i, x in enumerate(mine):
    d = [dict(zip(s, v)) for s, v in zip(x['sets'], x['vals'])]
    if not c4k_core.is_core(d)[0] or len(x['sets']) != 4: continue
    hit = [j for j, cg in enumerate(CG) if nx.is_isomorphic(G(x['sets']), cg, node_match=nm)]
    print('my strict core %2d: isomorphic to certifier instance(s) %s' % (i, hit), '' if hit else '  <-- NOT AMONG THE 11', flush=True)


def rows(c):
    m = 1 + max(max(s) for s in c['sets'])
    return [[dict(zip(s, v)).get(g, 0) for g in range(m)] for s, v in zip(c['sets'], c['vals'])]


def starved_all(V, y):
    n, m = len(V), len(V[0]); J = set(range(m)) - set(y); ok = True; md = 0
    for own in itertools.product(range(n), repeat=m):
        X = [[g for g in range(m) if own[g] == i] for i in range(n)]
        if not all(VZ.val(V, i, X[i]) >= V[i][y[i]] for i in range(n)) or not VZ.efx0(V, X): continue
        md += 1; st = False
        for a in range(n):
            if y[a] in X[a]: continue
            best = sum(V[a][g] for g in X[a] if g in J) + max([V[a][f] for f in X[a] if f in y] + [0])
            if best <= V[a][y[a]]: st = True
        ok &= st
    return ok, md


for j, c in enumerate(cert):
    V = rows(c); res, _ = rndlib.oc1z(V)
    for r in res:
        if not r['perfect'] or r['OC1'] > 0: continue
        st, md = starved_all(V, list(r['picks']))
        b = VZ.brute(V, r['order'])
        print('certifier %2d order %s picks %s | every MD allocation starved: %s (%d MD) | OC1\' rnd.c %s forward %s | two rounds %s'
              % (j, r['order'], list(r['picks']), st, md, r['OC1P'] > 0, VZ.oc1_prime(V, r['order']), b.get('two_rounds_1')), flush=True)
