"""Cross-check rnd.c's zero-aware OC1 (rnd_oc1z) against k4/sdc's pipeline (verify_k4zero.sdc_pipeline: Enc +
de_free.moves with rings + oc_absorb.extends_A) at every perfect start: random k-limited instances with zeros and the
zero versions of every eps-failure found (kgen/rounds.md §4.5).
    python3 kgen/rounds/xcheck_z.py T SEED"""
import sys, os, json, random, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import rndlib, verify_k4zero as VZ
T, seed = int(sys.argv[1]), int(sys.argv[2]); rng = random.Random(seed)
R = os.path.join(HERE, '..', '..', 'results', 'kgen_rounds')
insts = []
for fn in ('fails_keps.jsonl', 'fails_kcover.jsonl', 'fails_kcore.jsonl'):
    for l in open(os.path.join(R, fn)):
        V = json.loads(l)['vals']
        if len(V) <= 4: insts.append([[x if x > 5 else 0 for x in r] for r in V])
for t in range(T):
    n = rng.choice([3, 4]); m = rng.randint(n + 1, 7)
    V = []
    for i in range(n):
        k = rng.randint(2, 4); S = rng.sample(range(m), k)
        V.append([rng.randint(1, 60) if g in S else 0 for g in range(m)])
    insts.append(V)
C = collections.Counter(); bad = 0
for V in insts:
    res, _ = rndlib.oc1z(V)
    for r in res:
        if not r['perfect']: continue
        a = VZ.sdc_pipeline(V, r['order'])
        if list(a['picks']) != list(r['picks']): print('PICKS DIFFER', V, r['order'], a['picks'], r['picks']); bad += 1; continue
        c = r['OC1'] > 0; C[('OC1', c)] += 1
        e = r['EXT1'] > 0; C[('EXT1', e)] += 1
        if c != a['oc1'] or e != a['ext_1']:
            bad += 1; print('MISMATCH', json.dumps(V), r['order'], 'C', e, c, 'sdc', a['ext_1'], a['oc1'], flush=True)
print(dict(C)); print('mismatches', bad)
