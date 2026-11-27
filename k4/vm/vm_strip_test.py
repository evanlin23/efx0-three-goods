"""F5 (final exchange): vmlib.vm_strip_run over every resolution of the choice points (DFS up to --limit, then random
samples).  Per instance: some run EFX0 / every run.  EVIDENCE only.
    python3 k4/vm/vm_strip_test.py SOURCE [--limit=N] [--samples=N]"""
import sys, os, collections, json, random, time, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
from vm_test import items_for

VARS = {'strip-rot': dict(rot=True), 'strip': dict(rot=False), 'strip-rot-first': dict(rot=True, which='first')}


def one(args):
    name, sets, vals, m, limit, samples = args
    I = V.Inst(sets, vals, m); out = {}
    for v, kw in VARS.items():
        st = collections.Counter(); kinds = collections.Counter()
        runs = list(V.all_runs(V.vm_strip_run, I, limit=limit, **kw))
        if len(runs) >= limit:
            rng = random.Random(5)
            for t in range(samples):
                c = V.Chooser((), rng=rng)
                try: r = V.vm_strip_run(I, c, **kw)
                except V.Stuck as e: r = e
                runs.append((c.made, r))
        for ch, r in runs:
            st['runs'] += 1
            if isinstance(r, V.Stuck):
                kinds[r.args[0][0]] += 1
            else:
                assert V.is_efx0(I, r[0]), (name, v, ch)
                st['ok'] += 1
        out[v] = (st['runs'], st['ok'], dict(kinds))
    return name, I.n, I.m, out


if __name__ == '__main__':
    src = sys.argv[1]
    opt = dict(a[2:].split('=') for a in sys.argv[2:] if a.startswith('--'))
    limit = int(opt.get('limit', 2000)); samples = int(opt.get('samples', 200))
    print('$ python3 k4/vm/vm_strip_test.py', ' '.join(sys.argv[1:]))
    C = collections.Counter(); K = collections.Counter(); bad = collections.defaultdict(list); t0 = time.time()
    with mp.Pool(os.cpu_count()) as pool:
        for name, n, m, out in pool.imap_unordered(one, [(a, b, c, d, limit, samples) for a, b, c, d in items_for(src)], chunksize=4):
            C['instances'] += 1
            for v, (runs, ok, kinds) in out.items():
                C[v + ': some run EFX0'] += ok > 0; C[v + ': every run EFX0'] += ok == runs
                for k, c in kinds.items(): K[(v, k)] += c
                if ok == 0: bad[v].append((n, m, name))
    for k in sorted(C): print('%-40s %d' % (k, C[k]))
    for k in sorted(K): print('  stuck kind', k, K[k])
    for v, L in bad.items():
        print('  %s: no EFX0 run (%d):' % (v, len(L)), ', '.join('%s(n=%d,m=%d)' % (nm, n, m) for n, m, nm in sorted(L)[:8]))
    print('time %.0f s' % (time.time() - t0))
