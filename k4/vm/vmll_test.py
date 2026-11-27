"""The deterministic algorithm VM-LL (vmlib.vm6x_run, mode eagerLL, rotation; every choice point resolved by its
first option, i.e. index tie-breaks): run once per instance, check the output against the raw EFX0 definition, list
the failures (smallest first).  EVIDENCE only.
    python3 k4/vm/vmll_test.py SOURCE [SOURCE ...] [--relabel=K]   (K random relabellings of agents and goods each)"""
import sys, os, json, random, time, collections, zlib, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
from vm_test import items_for


def relabel(sets, vals, m, rng):
    n = len(sets); pa = list(range(n)); rng.shuffle(pa); pg = list(range(m)); rng.shuffle(pg)
    S = [None] * n; W = [None] * n
    for i in range(n):
        S[pa[i]] = [pg[g] for g in sets[i]]; W[pa[i]] = list(vals[i])
    return S, W


def one(args):
    name, sets, vals, m = args
    I = V.Inst(sets, vals, m); t = time.time()
    try:
        X, fl = V.vm6x_run(I, V.Chooser(()), mode='eagerLL')
        ok = V.is_efx0(I, X); assert ok, name
        return name, I.n, I.m, sets, vals, True, time.time() - t, None
    except V.Stuck as e:
        return name, I.n, I.m, sets, vals, False, time.time() - t, str(e.args[0])[:300]


if __name__ == '__main__':
    srcs = [a for a in sys.argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=') for a in sys.argv[1:] if a.startswith('--'))
    K = int(opt.get('relabel', 0))
    print('$ python3 k4/vm/vmll_test.py', ' '.join(sys.argv[1:]))
    items = []
    for src in srcs:
        for nm, s, v, m in items_for(src):
            items.append((nm, s, v, m))
            rng = random.Random(zlib.crc32(nm.encode()))
            for k in range(K):
                S, W = relabel(s, v, m, rng); items.append(('%s~%d' % (nm, k), S, W, m))
    C = collections.Counter(); bad = []; tmax = 0; t0 = time.time()
    with mp.Pool(os.cpu_count()) as pool:
        for name, n, m, sets, vals, ok, dt, why in pool.imap_unordered(one, items, chunksize=8):
            C['instances'] += 1; C['EFX0'] += ok; tmax = max(tmax, dt)
            if not ok: bad.append((n, m, sum(map(len, sets)), name, sets, vals, why))
    for k in sorted(C): print('%-12s %d' % (k, C[k]))
    print('failures', len(bad))
    for n, m, s, name, sets, vals, why in sorted(bad)[:10]:
        print('  FAIL %s n=%d m=%d %s %s' % (name, n, m, json.dumps({'sets': sets, 'vals': vals, 'm': m}), why))
    print('slowest instance %.2f s; time %.0f s' % (tmax, time.time() - t0))
