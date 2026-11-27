"""Cross-check rnd.c's zero-aware round classes (RND1Z: one round; RNDPZ: ROUND-P; RNDOZ: a round of OC1' moves) against the forward
verify_k4zero.round_pool at every perfect start: the certifier's 11 (n = 4) and 24 (n = 5) and random k-limited
instances with zeros (kgen/rounds.md §4.9).
    python3 kgen/rounds/xcheck_roundz.py T SEED [N5]"""
import sys, os, json, random, collections, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import rndlib, verify_k4zero as VZ
T, seed = int(sys.argv[1]), int(sys.argv[2]); N5 = int(sys.argv[3]) if len(sys.argv) > 3 else 24
rng = random.Random(seed); R = os.path.join(HERE, '..', '..', 'results', 'kgen_rounds')
def rows(sets, vals):
    m = 1 + max(max(s) for s in sets); V = [[0] * m for _ in sets]
    for i, (s, vv) in enumerate(zip(sets, vals)):
        for g, x in zip(s, vv): V[i][g] = x
    return V
insts = [rows(c['sets'], c['vals']) for c in json.load(open(os.path.join(R, 'certifier_oc1max_cex_n4.json')))['instances']]
for t, l in enumerate(open(os.path.join(R, 'certifier_oc1prime_cex_n5.jsonl'))):
    if t < N5: x = json.loads(l); insts.append(rows(x['sets'], x['vals']))
for t in range(T):
    n = rng.choice([3, 4]); m = rng.randint(n + 1, 7); V = []
    for i in range(n):
        S = rng.sample(range(m), rng.randint(2, 4)); V.append([rng.randint(1, 60) if g in S else 0 for g in range(m)])
    insts.append(V)
C = collections.Counter(); bad = 0; t0 = time.time()
for V in insts:
    res, _ = rndlib.oc1z(V)
    for r in res:
        if not r['perfect']: continue
        for k, pooled, oc in (('RND1Z', False, False), ('RNDPZ', True, False), ('RNDOZ', True, True)):
            c = r[k] > 0; b = VZ.round_pool_ok(V, r['order'], pooled, own_chain=oc)
            C[(k, c)] += 1
            if b != c: bad += 1; print('MISMATCH', k, json.dumps(V), r['order'], 'C', c, 'forward', b, flush=True)
        if r['RNDPZ'] == 0:   # the wider variant (t = 0 agents may take end picks too), forward only
            C[('RNDPZ+adders', VZ.round_pool_ok(V, r['order'], True, adders=True))] += 1
print(dict(C)); print('mismatches', bad, '%.0f s' % (time.time() - t0))
