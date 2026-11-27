"""Does some state of the reconstructed V-M algorithm extend to a complete EFX0 allocation?  For every resolution of
the choice points up to a stage (stop=II: the one-good matching of Phases I-II; stop=IIIm: after Phase III's
matchings), SAT-check (k4/sdc/sdclib.Enc, the exact EFX0 encoding) whether some complete EFX0 allocation contains it.
EVIDENCE only.

    python3 k4/vm/vm_extend.py SOURCE [--stop=II|IIIm] [--limit=N]
"""
import sys, os, json, collections, time, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
import data
data._sdc()
from sdclib import Enc
from pysat.solvers import Cadical153
from vm_test import items_for


def completable(E, X):
    cl = list(E.cl)
    for g in range(E.m):
        cl.append([-E.x[g][E.n]])
    for i, B in enumerate(X):
        for g in B:
            cl.append([E.x[g][i]])
    S = Cadical153(bootstrap_with=cl); ok = S.solve(); S.delete()
    return ok


def one(args):
    name, sets, vals, m, stop, limit = args
    I = V.Inst(sets, vals, m); E = Enc(sets, vals, m)
    seen = {}
    for ch, res in V.all_runs(V.vm_run, I, limit=limit, stop=stop):
        if isinstance(res, V.Stuck):
            continue
        X, fl = res
        key = tuple(tuple(sorted(b)) for b in X)
        if key not in seen:
            seen[key] = completable(E, X)
    anyc = completable(E, [[] for _ in range(I.n)])
    return name, I.n, I.m, len(seen), sum(seen.values()), anyc, [list(k) for k, v in seen.items() if not v][:1]


def main():
    src = sys.argv[1]
    opt = dict(a[2:].split('=') for a in sys.argv[2:] if a.startswith('--'))
    stop = opt.get('stop', 'II'); limit = int(opt.get('limit', 5000))
    print('$ python3 k4/vm/vm_extend.py', ' '.join(sys.argv[1:]))
    t0 = time.time(); C = collections.Counter(); bad = []
    items = items_for(src)
    with mp.Pool(os.cpu_count()) as pool:
        for name, n, m, ns, nc, anyc, ex in pool.imap_unordered(one, [(a, b, c, d, stop, limit) for a, b, c, d in items]):
            C['instances'] += 1; C['states'] += ns; C['states extendable'] += nc
            C['instances: some state extends'] += nc > 0
            C['instances: every state extends'] += nc == ns
            C['instances with an EFX0 allocation'] += anyc
            if nc == 0:
                bad.append((n, m, name, ex))
    for k in sorted(C): print('%-40s %d' % (k, C[k]))
    for n, m, name, ex in sorted(bad)[:10]:
        print('no state extends:', name, 'n=%d m=%d' % (n, m), json.dumps(ex))
    print('time %.0f s' % (time.time() - t0))


if __name__ == '__main__':
    main()
