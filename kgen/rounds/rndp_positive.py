"""The zero-aware ROUND-P (RNDPZ, kgen/rounds.md §4.9: only non-end agents of chains with t >= 1 take end goods) and
one plain round (RND1Z) at the positive-value one-round failures (fails*.jsonl: ROUND+ failures, starvation) and at
X4 (the ROUND-X failure, §4.2).  rnd.c, re-checked by the forward verify_k4zero.round_pool.
    python3 kgen/rounds/rndp_positive.py"""
import sys, os, json, glob, collections, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import rndlib, verify_k4zero as VZ
R = os.path.join(HERE, '..', '..', 'results', 'kgen_rounds'); t0 = time.time()
X4 = [[1,642,31,987,363,2866,764], [136,705,266,1148,475,2515,985], [146,133,242,1670,1,2701,633], [245,119,75,2148,140,2806,653]]
items = [('X4', X4, (3, 1, 0, 2))]
for fn in sorted(glob.glob(os.path.join(R, 'fails*.jsonl'))):
    if 'rndpz' in fn: continue
    for l in open(fn):
        x = json.loads(l); V = x.get('vals')
        if V is None or any(v <= 0 for row in V for v in row): continue
        items.append((os.path.basename(fn), V, tuple(x['order']) if 'order' in x else None))
C = collections.Counter(); bad = 0; seen = set()
for fam, V, o in items:
    res, _ = rndlib.oc1z(V)
    for r in res:
        if o is not None and tuple(r['order']) != o and tuple(r['picks']) != tuple(rndlib.sd(V, o)): continue
        if r['RND1Z'] > 0 and o is None: continue
        key = (json.dumps(V), tuple(r['picks']))
        if key in seen: continue
        seen.add(key)
        a, b = r['RND1Z'] > 0, r['RNDPZ'] > 0
        C[(fam, 'RND1Z', a)] += 1; C[(fam, 'RNDPZ', b)] += 1
        if len(V) * len(V[0]) <= 36:
            fa = VZ.round_pool_ok(V, r['order'], False); fb = VZ.round_pool_ok(V, r['order'], True)
            C[('forward checked',)] += 1
            if (fa, fb) != (a, b): bad += 1; print('MISMATCH', fam, json.dumps(V), r['order'], (a, b), (fa, fb), flush=True)
        if not b: print('RNDPZ FAILS', fam, json.dumps(V), 'order', r['order'], 'picks', r['picks'], 'MD', r['MD'], flush=True)
for k in sorted(C, key=str): print(k, C[k])
print('mismatches', bad, '%.0fs' % (time.time() - t0))
