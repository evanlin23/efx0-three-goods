"""Cross-check rnd.c's ROUND-X and ROUND-P classes (RNDX, RNDX1, RNDP, RNDP1) against bruter.rounds_pool (forward,
from the definition) on the n = 4 one-round failures of fails.jsonl and random small instances.
    python3 kgen/rounds/xcheck_x.py T SEED       random small instances (n = 3, 4) + the known one-round failures"""
import sys, os, json, random, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import rndlib, bruter, families
T, seed = int(sys.argv[1]), int(sys.argv[2]); rng = random.Random(seed)
R = os.path.join(HERE, '..', '..', 'results', 'kgen_rounds')
insts = [json.loads(l)['vals'] for l in open(os.path.join(R, 'fails.jsonl')) if len(json.loads(l)['vals']) == 4]
for t in range(T):
    n = rng.choice([3, 4]); m = rng.randint(n + 1, 7 if n == 3 else 6)
    insts.append(families.gen(rng.choice(families.KINDS), n, m, rng))
C = collections.Counter(); bad = 0
for V in insts:
    res, _ = rndlib.analyze(V); n = len(V)
    for r in res:
        for A, k, rc in ((1, 'RNDX1', False), (None, 'RNDX', False), (1, 'RNDP1', True), (None, 'RNDP', True)):
            b = bruter.round_x(V, r['order'], A, rc); c = r['counts'][k] > 0
            C[(k, c)] += 1
            if b != c: bad += 1; print('MISMATCH', k, json.dumps(V), r['order'], 'C', c, 'bruter', b, flush=True)
print(dict(C)); print('mismatches', bad)
