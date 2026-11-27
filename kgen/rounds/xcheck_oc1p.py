"""Cross-check rnd.c's OC1' (rnd_oc1z, bit OC1P) against verify_k4zero.oc1_prime (forward, from the definition) at every
perfect start: the zero versions of every eps-failure and random k-limited instances with zeros (kgen/rounds.md §4.6).
    python3 kgen/rounds/xcheck_oc1p.py T SEED"""
import sys, os, json, random, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import rndlib, verify_k4zero as VZ
T, seed = int(sys.argv[1]), int(sys.argv[2]); rng = random.Random(seed)
R = os.path.join(HERE, '..', '..', 'results', 'kgen_rounds')
insts = []; seen = set()
for fn in ('fails_keps.jsonl', 'fails_kcover.jsonl', 'fails_kcore.jsonl', 'fails_zcore.jsonl'):
    if not os.path.exists(os.path.join(R, fn)): continue
    for l in open(os.path.join(R, fn)):
        V = [[x if x > 5 else 0 for x in r] for r in json.loads(l)['vals']]
        if len(V) <= 4 and json.dumps(V) not in seen: seen.add(json.dumps(V)); insts.append(V)
for t in range(T):
    n = rng.choice([3, 4]); m = rng.randint(n + 1, 7); V = []
    for i in range(n):
        S = rng.sample(range(m), rng.randint(2, 4)); V.append([rng.randint(1, 60) if g in S else 0 for g in range(m)])
    insts.append(V)
C = collections.Counter(); bad = 0
for V in insts:
    res, _ = rndlib.oc1z(V)
    for r in res:
        if not r['perfect']: continue
        b = VZ.oc1_prime(V, r['order']); c = r['OC1P'] > 0
        C[('OC1P', c)] += 1; C[('OC1', r['OC1'] > 0)] += 1
        if b != c: bad += 1; print('MISMATCH', json.dumps(V), r['order'], 'C', c, 'forward', b, flush=True)
print(dict(C)); print('mismatches', bad)
