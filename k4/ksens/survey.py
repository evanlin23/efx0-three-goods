"""Random survey of SD-C, MD, OC and OC1 at larger k on junk-rich instances (k4/ksens.md), every order.

    python3 k4/ksens/survey.py KIND n K T SEED [JOBS]
Prints every failure (FAIL <conjecture> <instance> picks <Y>), then counts per start and per instance."""
import sys, json, random, collections, time, multiprocessing as mp
import _paths
import ocsat
from gen import gen


def job(args):
    kind, n, K, T, seed = args
    rng = random.Random(seed); C = collections.Counter(); fails = []
    for t in range(T):
        sets, vals = gen(kind, rng, n, K)
        m = 1 + max(max(s) for s in sets)
        res = ocsat.report(sets, vals, m)
        C['instances'] += 1; C['starts'] += len(res)
        for k in ('md', 'ext', 'oc', 'ext1', 'oc1'):
            C['starts %s' % k] += sum(r[k] for r in res.values())
        C['instances with a start needing a chain (OC1)'] += any(not r['ext1'] for r in res.values())
        C['instances with a start needing a chain (OC)'] += any(not r['ext'] for r in res.values())
        if not any(r['ext'] for r in res.values()): fails.append(('SD-C', sets, vals, None))
        for Y, r in res.items():
            for k in ('md', 'oc', 'oc1'):
                if not r[k]: fails.append((k.upper(), sets, vals, Y))
    return C, fails


if __name__ == '__main__':
    kind, n, K, T, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    jobs = int(sys.argv[6]) if len(sys.argv) > 6 else 4
    print('$ python3 k4/ksens/survey.py', *sys.argv[1:], flush=True); t0 = time.time()
    C = collections.Counter(); per = (T + jobs - 1) // jobs
    with mp.Pool(jobs) as p:
        for c, fails in p.imap_unordered(job, [(kind, n, K, per, seed * 1000 + j) for j in range(jobs)]):
            C.update(c)
            for f in fails: print('FAIL', f[0], json.dumps(f[1:3]), 'picks', f[3], flush=True)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
