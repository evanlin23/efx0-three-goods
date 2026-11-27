"""Is OC1' (kgen/rounds.md §4.6) enough at every n = 4 start where OC1^max fails?  Input: the certifier's export of
all 112,880 such (type profile, picks) pairs on the 11 failing n = 4 core hypergraphs
(results/k4_oc1max/two_move_starts_n4.json.gz on compute/k4-oc1max-cert, copied to
results/kgen_rounds/certifier_two_move_starts_n4.json.gz), where OC2^max (two moves) is certified.
For every start: rnd.c's zero-aware check (must report OC1 failing, consistency with the certifier) and OC1'; a random
sample is also checked by the forward brute force verify_k4zero.oc1_prime.
    python3 kgen/rounds/oc1p_vs_oc2.py [SAMPLE]"""
import sys, os, gzip, json, random, collections, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import rndlib, verify_k4zero as VZ
SAMPLE = int(sys.argv[1]) if len(sys.argv) > 1 else 300
d = json.load(gzip.open(os.path.join(HERE, '..', '..', 'results', 'kgen_rounds', 'certifier_two_move_starts_n4.json.gz')))
C = collections.Counter(); cache = {}; fails = []; sample = []; t0 = time.time(); rng = random.Random(1)
for h in d['hypergraphs']:
    sets = h['sets']; m = 1 + max(max(s) for s in sets)
    for st in h['starts']:
        V = [[0] * m for _ in sets]
        for i, (s, vv) in enumerate(zip(sets, st['vals'])):
            for g, x in zip(s, vv): V[i][g] = x
        key = json.dumps(V)
        if key not in cache:
            res, _ = rndlib.oc1z(V); cache[key] = {tuple(r['picks']): r for r in res}
        r = cache[key].get(tuple(st['picks']))
        C['starts'] += 1
        if r is None: C['picks not reproduced'] += 1; continue
        C['OC1 fails (agrees with certifier)' if r['OC1'] == 0 else 'OC1 HOLDS (disagrees)'] += 1
        if r['OC1P'] > 0: C["OC1' holds"] += 1
        else: C["OC1' FAILS"] += 1; fails.append((V, st['picks'], st['orders'][0]))
        if rng.random() < SAMPLE / 112880: sample.append((V, st['orders'][0], r['OC1P'] > 0))
    print(h['list'], h['idx'], dict(C), '%.0fs' % (time.time() - t0), flush=True)
print('TOTAL', dict(C))
bad = 0
for V, o, c in sample:
    b = VZ.oc1_prime(V, tuple(o))
    if b != c: bad += 1; print('SAMPLE MISMATCH', json.dumps(V), o, c, b)
print('forward brute force on a random sample of %d starts: %d mismatches' % (len(sample), bad))
for V, p, o in fails[:10]: print("OC1' FAILURE", json.dumps(V), 'picks', p, 'order', o)
