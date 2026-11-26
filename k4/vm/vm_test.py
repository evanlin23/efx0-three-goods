"""Run the reconstructed Viswanathan-Mehta algorithm (k4/vm/vmlib.py) under every reading and every resolution of its
choice points (DFS up to --limit runs per instance and reading, then --samples random runs), and check the outputs
against ordinary EFX and EFX0 (raw definitions).  EVIDENCE only.

    python3 k4/vm/vm_test.py SOURCE [--limit=N] [--samples=N] [--readings=all|main] [--show=K] [--jobs=J]
SOURCE: screen | suite | special | logs | cores:K:N:SEED (K = 3..6 agents) | gen:N:SEED[:nmax:mmax:vmax[:ties]]
"""
import sys, os, json, collections, random, time, zlib, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
import data

READINGS_ALL = [dict(rank=r, aout=a, n1a=n) for r in ('G', 'R') for a in ('matched', 'all') for n in (True, False)]
READINGS_MAIN = [dict(rank='G', aout='matched', n1a=True)]


def rname(rd):
    return 'rank=%s aout=%s n1a=%s' % (rd['rank'], rd['aout'], 'Y' if rd['n1a'] else 'N')


def group_of(fl, i):
    if i in fl['MA']: return 'A'
    for k in (1, 2, 3, 4):
        if i in fl['N'][k]:
            return 'N2r' if (k == 2 and i in fl['N2r']) else 'N%d' % k
    if i in fl['A']: return 'A-unmatched'
    return 'Nr'


def phase_of(fl, g):
    for tag, i, h in fl['log']:
        if h == g:
            return tag
    return '?'


def one(args):
    name, sets, vals, m, readings, limit, samples = args
    I = V.Inst(sets, vals, m)
    out = []
    for rd in readings:
        st = collections.Counter(); zero_kinds = collections.Counter(); ex = {}
        runs = []
        gen = V.all_runs(V.vm_run, I, limit=limit, record=True, **rd)
        for ch, res in gen:
            runs.append((ch, res))
        exhaustive = len(runs) < limit
        if not exhaustive:
            rng = random.Random(zlib.crc32(name.encode()))
            for t in range(samples):
                c = V.Chooser((), rng=rng)
                try:
                    res = V.vm_run(I, c, record=True, **rd)
                except V.Stuck as e:
                    res = e
                runs.append((c.made, res))
        for ch, res in runs:
            st['runs'] += 1
            if isinstance(res, V.Stuck):
                kind = res.args[0][0] if isinstance(res.args[0], tuple) else res.args[0]
                st['stuck:' + str(kind)] += 1
                ex.setdefault('stuck', (ch, str(res.args[0])[:300]))
                continue
            X, fl = res
            if 'claim_outside' in fl: st['claim_outside'] += 1
            e = V.is_efx(I, X); z = V.is_efx0(I, X)
            st['efx'] += e; st['efx0'] += z
            if not e:
                ex.setdefault('notefx', (ch, X, V.efx_violations(I, X, zero=False)[:4]))
            if e and not z:
                viol = V.efx_violations(I, X, zero=True)
                for (i, j, g) in viol:
                    if I.v[i].get(g, 0) == 0:
                        zero_kinds[(group_of(fl, i), group_of(fl, j), phase_of(fl, g))] += 1
                ex.setdefault('notefx0', (ch, X, viol[:4], {i: group_of(fl, i) for i in range(I.n)}))
        out.append((rname(rd), exhaustive, dict(st), dict(zero_kinds), ex))
    return name, I.n, I.m, out


def items_for(src):
    if src in ('screen', 'suite', 'special', 'logs'):
        return getattr(data, src)()
    if src.startswith('cores:'):
        _, K, N, seed = src.split(':')
        return data.random_cores(int(K), int(N), int(seed))
    if src.startswith('gen:'):
        p = src.split(':')
        kw = {}
        if len(p) > 3: kw['nmax'] = int(p[3])
        if len(p) > 4: kw['mmax'] = int(p[4])
        if len(p) > 5: kw['vmax'] = int(p[5])
        if len(p) > 6: kw['ties'] = p[6] == 'ties'
        return data.random_general(int(p[1]), int(p[2]), **kw)
    raise SystemExit('unknown source ' + src)


def main():
    src = sys.argv[1]
    opt = dict(a[2:].split('=') for a in sys.argv[2:] if a.startswith('--'))
    limit = int(opt.get('limit', 3000)); samples = int(opt.get('samples', 300)); show = int(opt.get('show', 3))
    readings = READINGS_ALL if opt.get('readings', 'main') == 'all' else READINGS_MAIN
    jobs = int(opt.get('jobs', os.cpu_count() or 2))
    print('$ python3 k4/vm/vm_test.py', ' '.join(sys.argv[1:]))
    t0 = time.time()
    items = items_for(src)
    args = [(nm, s, v, m, readings, limit, samples) for nm, s, v, m in items]
    agg = {rname(r): collections.Counter() for r in readings}
    zk = {rname(r): collections.Counter() for r in readings}
    exs = {rname(r): collections.defaultdict(list) for r in readings}
    with mp.Pool(jobs) as pool:
        for name, n, m, out in pool.imap_unordered(one, args, chunksize=4):
            for rn, exh, st, zero_kinds, ex in out:
                A = agg[rn]; A['instances'] += 1; A['exhaustive'] += exh
                A['runs'] += st.get('runs', 0)
                A['runs stuck'] += sum(v for k, v in st.items() if k.startswith('stuck'))
                A['runs not EFX'] += st['runs'] - sum(v for k, v in st.items() if k.startswith('stuck')) - st.get('efx', 0)
                A['runs EFX but not EFX0'] += st.get('efx', 0) - st.get('efx0', 0)
                A['runs claim_outside'] += st.get('claim_outside', 0)
                good = st.get('efx0', 0)
                A['inst: some run stuck'] += any(k.startswith('stuck') for k in st)
                A['inst: some run not EFX'] += ('notefx' in ex)
                A['inst: every run EFX'] += (st.get('efx', 0) == st['runs'])
                A['inst: some run EFX0'] += good > 0
                A['inst: every run EFX0'] += good == st['runs']
                zk[rn].update(zero_kinds)
                for k, v in ex.items():
                    exs[rn][k].append((n, m, name, v))
    for rn in agg:
        print('==', rn)
        for k in ['instances', 'exhaustive', 'runs', 'runs stuck', 'runs not EFX', 'runs EFX but not EFX0',
                  'runs claim_outside', 'inst: some run stuck', 'inst: some run not EFX', 'inst: every run EFX',
                  'inst: some run EFX0', 'inst: every run EFX0']:
            print('  %-28s %d' % (k, agg[rn][k]))
        if zk[rn]:
            print('  zero-good EFX0 violations (envier group, holder group, phase that placed the zero good): count')
            for k, v in zk[rn].most_common(12):
                print('    %-40s %d' % (k, v))
        for kind in ('stuck', 'notefx', 'notefx0'):
            L = sorted(exs[rn][kind], key=lambda t: (t[0], t[1]))[:show]
            for n, m, name, v in L:
                print('  example %s: %s (n=%d, m=%d) %s' % (kind, name, n, m, json.dumps(v, default=str)[:600]))
    print('time %.0f s' % (time.time() - t0))


if __name__ == '__main__':
    main()
