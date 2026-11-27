"""Cross-check of ocsat.py (SAT, sdclib's EFX0 clauses) against brute.py (enumeration from the definitions, numpy) on
random small instances, per start: md, ext, ext1, oc, oc1.

    python3 k4/ksens/xcheck_brute.py SEED T n mmin mmax K [KIND | small | seeds:LOG]"""
import sys, random, collections, time, json
import _paths
import ocsat, brute
from gen import gen

if __name__ == '__main__':
    seed, T, n, mmin, mmax, K = map(int, sys.argv[1:7]); kind = sys.argv[7] if len(sys.argv) > 7 else 'unif'
    rng = random.Random(seed); C = collections.Counter(); t0 = time.time()
    pool = None
    if kind.startswith('seeds:'):
        from climb import load_seeds
        pool = load_seeds(kind[6:]); T = min(T, len(pool))
    print('$ python3 k4/ksens/xcheck_brute.py', *sys.argv[1:], flush=True)
    while C['instances'] < T:
        if pool is not None:
            if C['instances'] + C['skipped'] >= len(pool): break
            sets, vals = pool[C['instances'] + C['skipped']]
            if len(sets) != n or 1 + max(max(x) for x in sets) > mmax: C['skipped'] += 1; continue
        elif kind != 'small':
            sets, vals = gen(kind, rng, n, K)
        if kind == 'small':
            m = rng.randint(mmin, mmax)
            sets = [sorted(rng.sample(range(m), rng.randint(2, min(K, m)))) for _ in range(n)]
            if len(set().union(*map(set, sets))) < m: continue
            vals = [rng.sample(range(1, 25), len(s)) for s in sets]
        m = 1 + max(max(s) for s in sets)
        if not (mmin <= m <= mmax): continue
        a = ocsat.report(sets, vals, m); b, _ = brute.report(sets, vals, m)
        C['instances'] += 1
        for Y in a:
            C['starts'] += 1
            for k in ('md', 'ext', 'ext1', 'oc', 'oc1'):
                C['%s %s' % (k, a[Y][k])] += 1
                if a[Y][k] != b[Y][k]:
                    C['MISMATCH ' + k] += 1; print('MISMATCH', k, json.dumps((sets, vals)), Y, a[Y][k], b[Y][k], flush=True)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
