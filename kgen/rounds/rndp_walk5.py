"""ROUND-P (RNDPZ), a round of OC1' moves (RNDOZ) and one plain round (RND1Z) at the matching session's n = 5 hard
starts near 5_pure#164 (results/k4_matching/n5_walk164.jsonl and n5_walk164_long.jsonl.gz on proof/k4-matching; read
with git show).  rnd.c counts at every row; for a random sample, the forward verify_k4zero.round_pool, and whether some
dangerous agent's earliest-wanter chain E(k) (k4/oc1max_multi.md §12) is a chain of some ROUND-P / RNDOZ witness round
(recs_vs_rndp.structures).
    python3 kgen/rounds/rndp_walk5.py FILE.jsonl[.gz] [SAMPLE]"""
import sys, os, gzip, json, random, collections, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import rndlib, verify_k4zero as VZ, recs_vs_rndp as RV
fn = sys.argv[1]; SAMPLE = int(sys.argv[2]) if len(sys.argv) > 2 else 100; rng = random.Random(5); t0 = time.time()
op = gzip.open if fn.endswith('.gz') else open
rows = [json.loads(l) for l in op(fn, 'rt') if l.strip()]
print('$ python3 kgen/rounds/rndp_walk5.py', *sys.argv[1:], '| rows', len(rows), flush=True)
C = collections.Counter(); sample = []
for x in rows:
    sets, vals = x['sets'], x['vals']; m = 1 + max(max(s) for s in sets); n = len(sets)
    V = [[0] * m for _ in sets]
    for i, (s, vv) in enumerate(zip(sets, vals)):
        for g, v in zip(s, vv): V[i][g] = v
    res, _ = rndlib.oc1z(V); r = next((r for r in res if list(r['picks']) == list(x['picks'])), None)
    if r is None: C['picks not reproduced'] += 1; continue
    C['rows'] += 1
    for k in ('OC1', 'OC1P', 'RND1Z', 'RNDOZ', 'RNDPZ'): C[(k, 'holds' if r[k] > 0 else 'FAILS')] += 1
    if r['RNDOZ'] == 0 or r['RNDPZ'] == 0: print('ROUND FAILS', json.dumps(x), {k: r[k] for k in ('RNDOZ', 'RNDPZ', 'MD')}, flush=True)
    if rng.random() < SAMPLE / len(rows): sample.append((V, x, r))
for V, x, r in sample:
    n, m = len(V), len(V[0]); y = tuple(x['picks']); o = tuple(x['orders'][0])
    fa = VZ.round_pool_ok(V, o, False); fo = VZ.round_pool_ok(V, o, True, own_chain=True); fp = VZ.round_pool_ok(V, o, True)
    if (fa, fo, fp) != (r['RND1Z'] > 0, r['RNDOZ'] > 0, r['RNDPZ'] > 0): C['FORWARD MISMATCH'] += 1; print('MISMATCH', json.dumps(x))
    C['forward checked'] += 1
    EK = RV.ek_chains(V, y, o); alls, _ = rndlib.list_efx(V)
    for mode, pooled in (('RNDOZ', False), ('RNDPZ', True)):
        chains = set()
        for ow in alls:
            X = [[g for g in range(m) if ow[g] == i] for i in range(n)]
            for cs in RV.structures(V, y, X, pooled) or []: chains |= set(cs)
        C[(mode, 'some dangerous E(k) is a witness chain', any(e in chains for e in EK.values()))] += 1
for k in sorted(C, key=str): print(k, C[k])
print('time %.0f s' % (time.time() - t0))
