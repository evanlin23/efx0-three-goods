"""Cross-check the brute force kgen/oc3.c against k4/sdc's SAT pipeline (oc_absorb.extends_A + de_free.iter_chains,
sets unbounded) on random three-agent instances: per order, chains needed by OC1 (0, 1 or None).

    python3 kgen/xcheck_oc3.py SEED N MMIN MMAX"""
import sys, random, collections, time, json
from oc3lib import brute, sat_check, status, ORD
from gen3 import gen

if __name__ == '__main__':
    seed, N, lo, hi = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter(); t0 = time.time()
    print('$ python3 kgen/xcheck_oc3.py', *sys.argv[1:], flush=True)
    kinds = ['klim:3', 'klim:4', 'klim:6', 'general', 'zeros', 'ident', 'junk', 'ties']
    for t in range(N):
        kind = kinds[t % len(kinds)]; m = rng.randint(lo, hi); v = gen(kind, m, rng)
        b = [status(d) for d in brute(v)]; s = sat_check(v)
        C['instances'] += 1; C['orders'] += 6
        for x in b: C['brute status %s' % x] += 1
        if b != s:
            C['MISMATCH'] += 1
            print('MISMATCH', kind, json.dumps(v), 'brute', b, 'sat', s, flush=True)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
