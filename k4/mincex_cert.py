"""Certify the candidate cores left by k4/mincex_shapes.py (k4/MINCEX.md, section 6): for every profile in the product
of the restricted type domains, an EFX0 allocation. CEGAR of k4/search4.py (model D2 first; profiles D2 misses are
solved without a shape limit), with the domains replaced by the restricted ones.
Usage: mincex_cert.py shapes.json.gz out.json.gz [--jobs=J]"""
import sys, json, gzip, time
from multiprocessing import Pool
import search4 as S4


def solve(rec):
    t0 = time.time()
    C = S4.Core(rec['n'], rec['m'], rec['sets'])
    C.dom = [[tuple(v) for v in d] for d in rec['domains']]
    C.cache = {}
    allocs, fails, complete = C.cegar(2, 1, 1000)
    assert complete, 'D2 CEGAR incomplete'
    extra = []
    for prof in fails:
        sol, x, z = C.inner(None, None)
        A = C.allocation(sol, x, z, prof)
        if A is None: return dict(rec, counterexample=[list(C.dom[i][t]) for i, t in enumerate(prof)])
        extra.append(A)
    return dict(rec, allocs=allocs + extra, d2_fails=len(fails), time=round(time.time() - t0, 1))


def main():
    src, out = sys.argv[1], sys.argv[2]
    opts = dict(a[2:].split('=', 1) for a in sys.argv[3:] if a.startswith('--') and '=' in a)
    recs = json.load(gzip.open(src, 'rt'))
    with Pool(int(opts.get('jobs', 4))) as pool:
        res = []
        for r in pool.imap(solve, recs):
            print('n = %d, m = %d, kinds %s, %d profiles: %s' % (
                r['n'], r['m'], ''.join(k[0] + k[1] for k in r['kinds']), r['profiles'],
                'COUNTEREXAMPLE %s' % r['counterexample'] if 'counterexample' in r else
                '%d allocations, %d D2 failures, %.1f s' % (len(r['allocs']), r['d2_fails'], r['time'])), flush=True)
            res.append(r)
    with gzip.open(out, 'wt') as f: json.dump(res, f)


if __name__ == '__main__':
    main()
