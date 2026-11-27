"""Kill-or-confirm the EFX0 repairs F1-F3 of k4/vm.md section 6 (vmlib.vm0_run), every resolution of the choice
points (DFS up to --limit, then random samples).  Per instance: does some run end EFX0 / does every run, and does some
V-M matching extend (the S1 test, vm_extend)?  EVIDENCE only.

    python3 k4/vm/vm0_test.py SOURCE [--variants=a,b,..] [--limit=N] [--samples=N]
variants: f2rot / f2 / nof2 / nof2rot, optionally +fixed (goods in index order in the F1 step)"""
import sys, os, json, collections, random, time, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
from vm_test import items_for
from vm_extend import completable, Enc

VARS = {'f2': dict(f2=True, rot=False), 'nof2': dict(f2=False, rot=False),
        'f2rot': dict(f2=True, rot=True), 'nof2rot': dict(f2=False, rot=True)}


def kw_of(v):
    base, _, fx = v.partition('+')
    kw = dict(VARS[base]); kw['order'] = 'fixed' if fx == 'fixed' else 'choice'
    return kw


def one(args):
    name, sets, vals, m, variants, limit, samples = args
    I = V.Inst(sets, vals, m); E = Enc(sets, vals, m)
    ext = False
    for ch, res in V.all_runs(V.vm_run, I, limit=3000, stop='II'):
        if not isinstance(res, V.Stuck) and completable(E, res[0]):
            ext = True; break
    out = {}
    for v in variants:
        kw = kw_of(v); st = collections.Counter(); ex = None
        runs = list(V.all_runs(V.vm0_run, I, limit=limit, **kw))
        if len(runs) >= limit:
            rng = random.Random(7)
            for t in range(samples):
                c = V.Chooser((), rng=rng)
                try: r = V.vm0_run(I, c, **kw)
                except V.Stuck as e: r = e
                runs.append((c.made, r))
        for ch, r in runs:
            st['runs'] += 1
            if isinstance(r, V.Stuck):
                st['stuck'] += 1
                if ex is None: ex = (ch, str(r.args[0])[:300])
                continue
            ok = V.is_efx0(I, r[0])
            if kw['f2']:
                assert ok, (name, v, ch, r[0])   # with F2 every step keeps EFX0 by construction; a failure is a bug
            if ok:
                st['efx0'] += 1
            else:
                st['notefx0'] += 1
        out[v] = (dict(st), ex)
    return name, I.n, I.m, ext, out


def main():
    src = sys.argv[1]
    opt = dict(a[2:].split('=') for a in sys.argv[2:] if a.startswith('--'))
    variants = opt.get('variants', 'f2,nof2,f2rot,nof2rot').split(',')
    limit = int(opt.get('limit', 2000)); samples = int(opt.get('samples', 200))
    print('$ python3 k4/vm/vm0_test.py', ' '.join(sys.argv[1:]))
    t0 = time.time(); C = collections.Counter(); exs = collections.defaultdict(list)
    items = items_for(src)
    with mp.Pool(os.cpu_count()) as pool:
        for name, n, m, ext, out in pool.imap_unordered(one, [(a, b, c, d, variants, limit, samples) for a, b, c, d in items], chunksize=4):
            C['instances'] += 1; C['S1 passes (some V-M matching extends)'] += ext
            for v, (st, ex) in out.items():
                some = st.get('efx0', 0) > 0; every = st.get('efx0', 0) == st['runs']
                C[v + ': some run EFX0'] += some; C[v + ': every run EFX0'] += every
                C[v + ': S1 passes, no run EFX0'] += ext and not some
                C[v + ': S1 fails, some run EFX0'] += (not ext) and some
                if ext and not some: exs[v].append((n, m, name, ex))
    for k in sorted(C): print('%-50s %d' % (k, C[k]))
    for v, L in exs.items():
        for n, m, name, ex in sorted(L)[:3]:
            print('  %s S1 passes, no run EFX0: %s n=%d m=%d %s' % (v, name, n, m, json.dumps(ex)[:400]))
    print('time %.0f s' % (time.time() - t0))


if __name__ == '__main__':
    main()
