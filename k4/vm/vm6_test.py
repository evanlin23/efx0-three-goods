"""F6 (upgrade moves, vmlib.vm6_run) over every resolution of the choice points (DFS up to --limit, then samples).
Per variant: instances with some EFX0 run / every run; the instances with no EFX0 run are listed (smallest first).
EVIDENCE only.
    python3 k4/vm/vm6_test.py SOURCE [--variants=eager,choice,eager-norot,x-choice,x-stuck,x-stuck-norot] [--limit=N] [--samples=N]"""
import sys, os, collections, json, random, time, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
from vm_test import items_for

VARS = {'eager': dict(upg='eager', rot=True), 'choice': dict(upg='choice', rot=True),
        'eager-norot': dict(upg='eager', rot=False), 'choice-norot': dict(upg='choice', rot=False),
        'x-choice': dict(mode='choice', rot=True, _x=True), 'x-stuck': dict(mode='stuck', rot=True, _x=True),
        'x-stuck-norot': dict(mode='stuck', rot=False, _x=True), 'x-eager': dict(mode='eager', rot=True, _x=True),
        'x-eager1': dict(mode='eager1', rot=True, _x=True), 'x-eagerL': dict(mode='eagerL', rot=True, _x=True),
        'x-eagerL1': dict(mode='eagerL1', rot=True, _x=True), 'x-eagerLL': dict(mode='eagerLL', rot=True, _x=True)}


def one(args):
    name, sets, vals, m, variants, limit, samples = args
    I = V.Inst(sets, vals, m); out = {}
    for v in variants:
        kw = dict(VARS[v]); ok = tot = 0; kinds = collections.Counter()
        run = V.vm6x_run if kw.pop('_x', False) else V.vm6_run
        runs = list(V.all_runs(run, I, limit=limit, **kw))
        if len(runs) >= limit:
            rng = random.Random(9)
            for t in range(samples):
                c = V.Chooser((), rng=rng)
                try: r = run(I, c, **kw)
                except V.Stuck as e: r = e
                runs.append((c.made, r))
        for ch, r in runs:
            tot += 1
            if isinstance(r, V.Stuck):
                kinds[r.args[0][0]] += 1
            else:
                assert V.is_efx0(I, r[0]), (name, v, ch); ok += 1
        first = not isinstance(runs[0][1], V.Stuck)
        out[v] = (tot, ok, dict(kinds), first)
    return name, I.n, I.m, sets, vals, out


if __name__ == '__main__':
    src = sys.argv[1]
    opt = dict(a[2:].split('=') for a in sys.argv[2:] if a.startswith('--'))
    variants = opt.get('variants', 'eager,choice').split(',')
    limit = int(opt.get('limit', 2000)); samples = int(opt.get('samples', 200))
    print('$ python3 k4/vm/vm6_test.py', ' '.join(sys.argv[1:]))
    C = collections.Counter(); K = collections.Counter(); bad = collections.defaultdict(list); t0 = time.time()
    with mp.Pool(os.cpu_count()) as pool:
        for name, n, m, sets, vals, out in pool.imap_unordered(one, [(a, b, c, d, variants, limit, samples) for a, b, c, d in items_for(src)], chunksize=4):
            C['instances'] += 1
            for v, (tot, ok, kinds, first) in out.items():
                C[v + ': some run EFX0'] += ok > 0; C[v + ': every run EFX0'] += ok == tot
                C[v + ': first run (all choices 0) EFX0'] += first
                if not first: bad[v + ' [first run]'].append((n, m, sum(map(len, sets)), name, sets, vals))
                C[v + ': runs'] += tot; C[v + ': runs EFX0'] += ok
                for k, c in kinds.items(): K[(v, k)] += c
                if ok == 0: bad[v].append((n, m, sum(map(len, sets)), name, sets, vals))
    for k in sorted(C): print('%-36s %d' % (k, C[k]))
    for k in sorted(K): print('  stuck kind', k, K[k])
    for v, L in bad.items():
        L.sort()
        print('  %s: no EFX0 run on %d:' % (v, len(L)), ', '.join('%s(n=%d,m=%d)' % (x[3], x[0], x[1]) for x in L[:12]))
        for x in L[:2]:
            print('    smallest:', x[3], json.dumps({'sets': x[4], 'vals': x[5], 'm': x[1]}))
    print('time %.0f s' % (time.time() - t0))
