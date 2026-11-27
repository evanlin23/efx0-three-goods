"""F4 test (k4/vm.md section 7): start the EFX0 repair (vmlib.vm0_run: Phase III with F2, then F1 with rotation, F3)
from every serial-dictatorship outcome instead of V-M's rank-greedy matching.  Per instance and SD outcome Y:
  ext(Y)  some complete EFX0 allocation contains Y (SAT, k4/sdc/sdclib.Enc)
  run(Y)  some resolution of vm0_run's choices from Y ends EFX0 (DFS up to --limit runs, then samples)
Reported: instances where some Y extends (SD-C), where some run(Y) succeeds, and outcomes with ext(Y) but not run(Y).
EVIDENCE only.
    python3 k4/vm/vm0_sd.py SOURCE [--limit=N] [--rot=1|0] [--maxorders=N]"""
import sys, os, json, itertools, collections, random, time, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
from vm_test import items_for
from vm_extend import completable, Enc


def sd(I, order):
    left = set(range(I.m)); Y = [None] * I.n
    for i in order:
        av = [g for g in I.rank[i] if g in left]
        if av:
            Y[i] = av[0]; left.discard(av[0])
    return Y


def some_run(I, Y, limit, rot):
    k = 0
    for ch, r in V.all_runs(V.vm0_run, I, limit=limit, base=Y, rot=rot):
        k += 1
        if not isinstance(r, V.Stuck) and V.is_efx0(I, r[0]):
            return True, k
    if k >= limit:
        rng = random.Random(3)
        for t in range(200):
            c = V.Chooser((), rng=rng)
            try:
                r = V.vm0_run(I, c, base=Y, rot=rot)
                if V.is_efx0(I, r[0]): return True, k + t
            except V.Stuck:
                pass
    return False, k


def one(args):
    name, sets, vals, m, limit, rot, maxorders = args
    I = V.Inst(sets, vals, m); E = Enc(sets, vals, m)
    rng = random.Random(1)
    orders = itertools.permutations(range(I.n)) if I.n <= 7 else (rng.sample(range(I.n), I.n) for _ in range(maxorders))
    seen = {}
    for o in orders:
        Y = tuple(sd(I, o))
        if Y in seen: continue
        e = completable(E, [[g] if g is not None else [] for g in Y])
        r, k = some_run(I, list(Y), limit, rot)
        seen[Y] = (e, r)
    ne = sum(e for e, r in seen.values()); nr = sum(r for e, r in seen.values())
    gap = [list(Y) for Y, (e, r) in seen.items() if e and not r]
    over = [list(Y) for Y, (e, r) in seen.items() if r and not e]
    return name, I.n, I.m, len(seen), ne, nr, gap, over


def main():
    src = sys.argv[1]
    opt = dict(a[2:].split('=') for a in sys.argv[2:] if a.startswith('--'))
    limit = int(opt.get('limit', 1000)); rot = opt.get('rot', '1') == '1'; maxorders = int(opt.get('maxorders', 300))
    print('$ python3 k4/vm/vm0_sd.py', ' '.join(sys.argv[1:]))
    t0 = time.time(); C = collections.Counter(); gaps = []
    items = items_for(src)
    with mp.Pool(os.cpu_count()) as pool:
        for name, n, m, ns, ne, nr, gap, over in pool.imap_unordered(one, [(a, b, c, d, limit, rot, maxorders) for a, b, c, d in items], chunksize=2):
            C['instances'] += 1; C['SD outcomes'] += ns; C['SD outcomes that extend'] += ne
            C['SD outcomes with an EFX0 run'] += nr
            C['instances: some SD outcome extends (SD-C)'] += ne > 0
            C['instances: some SD outcome has an EFX0 run'] += nr > 0
            C['outcomes: extends, no EFX0 run'] += len(gap)
            C['outcomes: no extension, EFX0 run (rotation moved the base)'] += len(over)
            C['instances: no SD outcome extends, some EFX0 run'] += (ne == 0 and nr > 0)
            if gap: gaps.append((n, m, name, gap[:2]))
    for k in sorted(C): print('%-50s %d' % (k, C[k]))
    for n, m, name, g in sorted(gaps)[:8]:
        print('  extends but no EFX0 run:', name, 'n=%d m=%d' % (n, m), json.dumps(g))
    print('time %.0f s' % (time.time() - t0))


if __name__ == '__main__':
    main()
