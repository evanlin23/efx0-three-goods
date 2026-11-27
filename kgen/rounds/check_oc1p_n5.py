"""The certifier's n = 5 counterexamples to OC1'^max (results/k4_oc1max/oc1prime_cex_n5_partial.jsonl on
compute/k4-oc1max-cert, copied to results/kgen_rounds/certifier_oc1prime_cex_n5.jsonl): check each with rnd.c (OC1,
OC1', MD) and with the forward brute force (oc1_prime); find an order giving the picks; core test; and the mechanism:
in every MD EFX0 allocation, which agents are starved, how many foreign picks each holds, and whether two rounds repair.
    python3 kgen/rounds/check_oc1p_n5.py [N]"""
import sys, os, json, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import rndlib, verify_k4zero as VZ, c4k_core
N = int(sys.argv[1]) if len(sys.argv) > 1 else 99
R = os.path.join(HERE, '..', '..', 'results', 'kgen_rounds')
C = collections.Counter()
for t, line in enumerate(open(os.path.join(R, 'certifier_oc1prime_cex_n5.jsonl'))):
    if t >= N: break
    x = json.loads(line); sets = x['sets']; m = 1 + max(max(s) for s in sets); n = len(sets)
    V = [[0] * m for _ in sets]
    for i, (s, vv) in enumerate(zip(sets, x['vals'])):
        for g, v in zip(s, vv): V[i][g] = v
    d = [dict(zip(s, vv)) for s, vv in zip(sets, x['vals'])]
    core = c4k_core.is_core(d)[0]
    res, _ = rndlib.oc1z(V)
    r = next((r for r in res if list(r['picks']) == x['picks']), None)
    if r is None: print(t, 'picks not an SD outcome here'); C['picks?'] += 1; continue
    fw = VZ.oc1_prime(V, r['order'])
    # mechanism: MD EFX0 allocations and starvation profile
    y = x['picks']; J = set(range(m)) - set(y); prof = collections.Counter(); md = 0
    L, _ = rndlib.list_efx(V)
    for own in L:
        X = [[g for g in range(m) if own[g] == i] for i in range(n)]
        if not all(VZ.val(V, i, X[i]) >= V[i][y[i]] for i in range(n)): continue
        md += 1; st = []
        for a in range(n):
            if y[a] in X[a]: continue
            fp = [f for f in X[a] if f in y]
            best = sum(V[a][g] for g in X[a] if g in J) + max([V[a][f] for f in fp] + [0])
            if best <= V[a][y[a]]: st.append((a, len(fp)))
        prof[tuple(st)] += 1
    two = VZ.brute(V, r['order']).get('two_rounds_1') if n <= 5 else None
    C[('OC1 fails', r['OC1'] == 0)] += 1; C[("OC1' fails rnd.c", r['OC1P'] == 0)] += 1; C[("OC1' fails forward", not fw)] += 1
    print('%2d %s idx %s core %s order %s | OC1 %d OC1\' %d (forward %s) MD %d | starved (agent, #foreign picks) per MD: %s | two rounds %s'
          % (t, x['list'], x['idx'], core, r['order'], r['OC1'], r['OC1P'], fw, md, dict(prof), two), flush=True)
print(dict(C))
