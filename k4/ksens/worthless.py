"""OC and OC1 with goods nobody values (k4/ksens.md).  TARGET4 allows such goods; in an EFX0 allocation they can only
sit in bundles nobody envies, and OC1 counts them as junk.  Take logged instances (every [sets, vals] pair in the given
logs, n <= NMAX), add Z goods valued by nobody, and test every order.

    python3 k4/ksens/worthless.py Z NMAX LOG [LOG ...]"""
import sys, json, collections, time
import _paths
import ocsat
from climb import load_seeds

if __name__ == '__main__':
    Z, NMAX = int(sys.argv[1]), int(sys.argv[2]); C = collections.Counter(); t0 = time.time(); seen = set()
    print('$ python3 k4/ksens/worthless.py', *sys.argv[1:], flush=True)
    for f in sys.argv[3:]:
        for sets, vals in load_seeds(f):
            key = json.dumps((sets, vals))
            if key in seen or len(sets) > NMAX: continue
            seen.add(key)
            m = 1 + max(max(s) for s in sets) + Z
            res = ocsat.report(sets, vals, m)
            C['instances'] += 1; C['starts'] += len(res)
            for k in ('md', 'ext', 'oc', 'ext1', 'oc1'):
                C['starts %s' % k] += sum(r[k] for r in res.values())
            for k in ('md', 'oc', 'oc1'):
                bad = [Y for Y, r in res.items() if not r[k]]
                if bad:
                    C['instances failing %s' % k] += 1
                    if C['shown ' + k] < 5:
                        C['shown ' + k] += 1
                        print('FAIL', k.upper(), json.dumps((sets, vals)), 'm', m, 'picks', bad[0], 'order', res[bad[0]]['order'], flush=True)
            if not any(r['ext'] for r in res.values()): C['instances failing SD-C'] += 1
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
