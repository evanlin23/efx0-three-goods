"""One plain round (RND1Z) and ROUND-P (RNDPZ), zero-aware (kgen/rounds.md §4.9), at every known k = 4 failure start:
the certifier's 112,880 n = 4 OC1^max-failing starts (certifier_two_move_starts_n4.json.gz), every perfect start of the
certifier's 11 n = 4 and 24 n = 5 hypergraphs (OC1^max / OC1' counterexamples), C4K, and the zero-core climb failures
(zcore_fails.json, zcore_fails_n6.json).  rnd.c counts; failures (at most FCAP = 400 per family, at random) and a random
sample of the rest are re-checked by the forward verify_k4zero.round_pool (independent code).
    python3 kgen/rounds/rndp_known.py [SAMPLE]"""
import sys, os, gzip, json, random, collections, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import rndlib, verify_k4zero as VZ
SAMPLE = int(sys.argv[1]) if len(sys.argv) > 1 else 200
R = os.path.join(HERE, '..', '..', 'results', 'kgen_rounds'); rng = random.Random(3); t0 = time.time()


def rows(sets, vals):
    m = 1 + max(max(s) for s in sets); V = [[0] * m for _ in sets]
    for i, (s, vv) in enumerate(zip(sets, vals)):
        for g, x in zip(s, vv): V[i][g] = x
    return V


fwd = []   # (family, V, order, C RND1Z holds, C RNDPZ holds)


def scan(fam, V, C, only=None, oc1fail=False):
    res, _ = rndlib.oc1z(V)
    for r in res:
        if not r['perfect']: continue
        if only is not None and tuple(r['picks']) != tuple(only): continue
        if oc1fail and r['OC1'] > 0: continue
        a, b = r['RND1Z'] > 0, r['RNDPZ'] > 0
        C[(fam, 'starts')] += 1; C[(fam, 'RND1Z holds' if a else 'RND1Z FAILS')] += 1
        C[(fam, 'RNDPZ holds' if b else 'RNDPZ FAILS')] += 1
        if not a or not b or rng.random() < SAMPLE / 113000: fwd.append((fam, V, r['order'], a, b))


C = collections.Counter(); cache = set()
d = json.load(gzip.open(os.path.join(R, 'certifier_two_move_starts_n4.json.gz')))
for h in d['hypergraphs']:
    for st in h['starts']:
        V = rows(h['sets'], st['vals']); scan('two_move_n4', V, C, only=st['picks'])
print('112,880 starts', {k[1]: v for k, v in C.items() if k[0] == 'two_move_n4'}, '%.0fs' % (time.time() - t0), flush=True)
for c in json.load(open(os.path.join(R, 'certifier_oc1max_cex_n4.json')))['instances']:
    scan('cert11_n4_OC1fail', rows(c['sets'], c['vals']), C, oc1fail=True)
for l in open(os.path.join(R, 'certifier_oc1prime_cex_n5.jsonl')):
    x = json.loads(l); scan('cert24_n5_OC1fail', rows(x['sets'], x['vals']), C, oc1fail=True)
c4k = json.load(open(os.path.join(R, 'c4k.json')))
c4k = c4k['vals'] if isinstance(c4k, dict) and 'vals' in c4k else c4k
if isinstance(c4k, list) and isinstance(c4k[0], dict): c4k = rows(c4k[0]['sets'], c4k[0]['vals'])
scan('C4K_OC1fail', c4k, C, oc1fail=True)
for fn in ('zcore_fails.json', 'zcore_fails_n6.json'):
    for x in json.load(open(os.path.join(R, fn))): scan('zcore_OC1fail', rows(x['sets'], x['vals']), C, oc1fail=True)
for k in sorted(C): print(k, C[k])
FCAP = 400   # forward re-check at most FCAP random entries per (family, C verdict)
grp = collections.defaultdict(list)
for x in fwd: grp[(x[0], x[3], x[4])].append(x)
fwd = [x for k in sorted(grp, key=str) for x in (grp[k] if len(grp[k]) <= FCAP else rng.sample(grp[k], FCAP))]
bad = 0; FC = collections.Counter()
for fam, V, o, a, b in fwd:
    fa = VZ.round_pool_ok(V, tuple(o), False); fb = VZ.round_pool_ok(V, tuple(o), True)
    FC[(fam, 'RND1Z', fa)] += 1; FC[(fam, 'RNDPZ', fb)] += 1
    if fa != a or fb != b: bad += 1; print('MISMATCH', fam, json.dumps(V), o, 'C', a, b, 'forward', fa, fb, flush=True)
for k in sorted(FC, key=str): print('forward', k, FC[k])
print('forward re-check of %d starts (failures, capped, + random sample): %d mismatches, %.0fs' % (len(fwd), bad, time.time() - t0))
