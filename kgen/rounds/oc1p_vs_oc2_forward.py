"""Second implementation over ALL of the certifier's 112,880 OC1^max-failing n = 4 starts: OC1' by the forward brute
force verify_k4zero.oc1_prime (from the definition; no rnd.c).  Shard k of K.
    python3 kgen/rounds/oc1p_vs_oc2_forward.py K k"""
import sys, os, gzip, json, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import verify_k4zero as VZ
K, k = int(sys.argv[1]), int(sys.argv[2])
d = json.load(gzip.open(os.path.join(HERE, '..', '..', 'results', 'kgen_rounds', 'certifier_two_move_starts_n4.json.gz')))
i = -1; ok = 0; bad = 0; t0 = time.time()
for h in d['hypergraphs']:
    sets = h['sets']; m = 1 + max(max(s) for s in sets)
    for st in h['starts']:
        i += 1
        if i % K != k: continue
        V = [[0] * m for _ in sets]
        for a, (s, vv) in enumerate(zip(sets, st['vals'])):
            for g, x in zip(s, vv): V[a][g] = x
        assert VZ.sd(V, tuple(st['orders'][0])) == st['picks']
        if VZ.oc1_prime(V, tuple(st['orders'][0])): ok += 1
        else: bad += 1; print("OC1' FAILS", json.dumps(V), st['picks'], st['orders'][0], flush=True)
print('shard %d/%d: starts %d, OC1\' holds %d, fails %d (%.0f s)' % (k, K, ok + bad, ok, bad, time.time() - t0), flush=True)
