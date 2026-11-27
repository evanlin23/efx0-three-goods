"""VMX from every start: for every serial-dictatorship outcome Y (all orders; random orders for n > 7), does some run
of VMx (vmlib.vm6x_run, mode choice, rotation) started at Y end EFX0?  Since no step lowers a value, a success
value-dominates Y: a path form of Conjecture MD (K4.SDC.MD).  EVIDENCE only.
    python3 k4/vm/vm6_sd.py SOURCE [--limit=N] [--mode=choice] [--maxorders=N]"""
import sys, os, json, itertools, collections, random, time, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
from vm_test import items_for
from vm0_sd import sd


def some_run(I, Y, limit, mode):
    k = 0
    for ch, r in V.all_runs(V.vm6x_run, I, limit=limit, base=Y, mode=mode):
        k += 1
        if not isinstance(r, V.Stuck):
            assert V.is_efx0(I, r[0])
            assert all(I.val(i, r[0][i]) >= (I.v[i][Y[i]] if Y[i] is not None else 0) for i in range(I.n))
            return True
    if k >= limit:
        rng = random.Random(3)
        for t in range(100):
            c = V.Chooser((), rng=rng)
            try:
                V.vm6x_run(I, c, base=Y, mode=mode); return True
            except V.Stuck:
                pass
    return False


def one(args):
    name, sets, vals, m, limit, mode, maxorders = args
    I = V.Inst(sets, vals, m); rng = random.Random(1)
    orders = itertools.permutations(range(I.n)) if I.n <= 7 else (rng.sample(range(I.n), I.n) for _ in range(maxorders))
    outs = sorted(set(tuple(sd(I, o)) for o in orders), key=str)
    bad = [list(Y) for Y in outs if not some_run(I, list(Y), limit, mode)]
    return name, I.n, I.m, len(outs), bad


if __name__ == '__main__':
    src = sys.argv[1]
    opt = dict(a[2:].split('=') for a in sys.argv[2:] if a.startswith('--'))
    limit = int(opt.get('limit', 600)); mode = opt.get('mode', 'choice'); maxorders = int(opt.get('maxorders', 100))
    print('$ python3 k4/vm/vm6_sd.py', ' '.join(sys.argv[1:]))
    C = collections.Counter(); B = []; t0 = time.time()
    with mp.Pool(os.cpu_count()) as pool:
        for name, n, m, k, bad in pool.imap_unordered(one, [(a, b, c, d, limit, mode, maxorders) for a, b, c, d in items_for(src)], chunksize=2):
            C['instances'] += 1; C['SD outcomes'] += k; C['SD outcomes with no EFX0 run'] += len(bad)
            C['instances: every SD outcome has an EFX0 run'] += not bad
            if bad: B.append((n, m, name, bad[:3]))
    for k in sorted(C): print('%-50s %d' % (k, C[k]))
    for n, m, name, bad in sorted(B)[:10]:
        print('  no EFX0 run from', name, 'n=%d m=%d' % (n, m), json.dumps(bad))
    print('time %.0f s' % (time.time() - t0))
