"""CKMS's stopping states on the curated k = 4 instances (the DE4 screen set, k4/de4/ss_screen.py: GM4, A131, B131,
C127, D3 and the suite with n <= 5).  For each instance: RUNS runs of chlib.ckms with random tie-breaks, half from
the empty allocation, half from random serial-dictatorship picks; the stopping pools; checks as in ch_ckms.py.

    python3 kgen/charity/ch_screen.py SEED RUNS"""
import sys, os, json, random, collections, time, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
from chlib import from_sets, ckms, stuck_report, efx0, pool_ok
from ch_ckms import sd_start


def load():
    cwd = os.getcwd()
    sys.path.insert(0, os.path.join(ROOT, 'k4', 'de4')); sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
    os.chdir(os.path.join(ROOT, 'k4', 'de4'))
    from ss_screen import screen_set
    out = [(name, I.sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)], I.m) for name, I in screen_set()]
    os.chdir(cwd)
    return out


def job(args):
    name, sets, vals, m, seed, runs = args
    I = from_sets(sets, vals, m); rng = random.Random(seed)
    out = collections.Counter(); wit = []
    for r in range(runs):
        start = 'empty' if r % 2 == 0 else 'sd'
        X, P, c, tab = ckms(I, X=None if start == 'empty' else sd_start(I, rng), rng=rng)
        assert efx0(I, X) and pool_ok(I, X, P, strong=True)
        rep = stuck_report(I, X, P, tab)
        out['%s: pool %d' % (start, len(P))] += 1
        if P:                                   # continue with every champion option (robust stop)
            X, P, c, tab = ckms(I, X=X, rng=rng, mode='all')
            assert efx0(I, X) and pool_ok(I, X, P, strong=True)
            rep = stuck_report(I, X, P, tab)
            out['%s: robust pool %d' % (start, len(P))] += 1
        if P and len(wit) < 1:
            wit.append({'X': [sorted(B) for B in X], 'P': sorted(P), 'start': start, 'rep': rep})
    return name, I.n, I.m, out, wit


if __name__ == '__main__':
    seed, RUNS = map(int, sys.argv[1:3])
    print('$ python3 kgen/charity/ch_screen.py', *sys.argv[1:], flush=True)
    t0 = time.time(); C = collections.Counter(); inst = load()
    with mp.Pool(os.cpu_count()) as pool:
        for name, n, m, out, wit in pool.imap_unordered(job, [(a, b, c, d, seed * 7919 + t, RUNS)
                                                              for t, (a, b, c, d) in enumerate(inst)]):
            C['instances'] += 1
            for key, val in out.items():
                C[key] += val
            nz = sum(v for k, v in out.items() if 'robust' in k and not k.endswith('pool 0'))
            if nz:
                C['instances with a nonzero stop'] += 1
                print('NONZERO', name, n, m, dict(out), json.dumps(wit[0]), flush=True)
    for key in sorted(C):
        print(key, C[key])
    print('time %.0f s' % (time.time() - t0))
