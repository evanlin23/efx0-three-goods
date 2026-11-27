"""Distinct tops: does every run (or some run) of the EFX0 repair end EFX0?  Instances: random general 4-limited
instances and random core profiles, kept only if the agents' tops are pairwise distinct.  EVIDENCE only.
    python3 k4/vm/vm0_dt.py SOURCE [--variants=...] [--limit=N]"""
import sys, os, collections, json, random, time, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
from vm_test import items_for
from vm0_test import kw_of


def one(args):
    name, sets, vals, m, variants, limit = args
    I = V.Inst(sets, vals, m)
    tops = [r[0] for r in I.rank if r]
    if len(set(tops)) < len(tops):
        return None
    out = {}
    for v in variants:
        kw = kw_of(v); st = collections.Counter(); ex = None
        for ch, r in V.all_runs(V.vm0_run, I, limit=limit, **kw):
            st['runs'] += 1
            if isinstance(r, V.Stuck):
                st['stuck'] += 1; ex = ex or (ch, str(r.args[0])[:300])
            elif V.is_efx0(I, r[0]):
                st['efx0'] += 1
            else:
                st['notefx0'] += 1; ex = ex or (ch, r[0])
        out[v] = (dict(st), ex)
    return name, I.n, I.m, sets, vals, out


if __name__ == '__main__':
    src = sys.argv[1]
    opt = dict(a[2:].split('=') for a in sys.argv[2:] if a.startswith('--'))
    variants = opt.get('variants', 'f2,f2+fixed').split(','); limit = int(opt.get('limit', 2000))
    print('$ python3 k4/vm/vm0_dt.py', ' '.join(sys.argv[1:]))
    C = collections.Counter(); bad = collections.defaultdict(list); t0 = time.time()
    with mp.Pool(os.cpu_count()) as pool:
        for res in pool.imap_unordered(one, [(a, b, c, d, variants, limit) for a, b, c, d in items_for(src)], chunksize=16):
            if res is None:
                C['skipped (tops not distinct)'] += 1; continue
            name, n, m, sets, vals, out = res
            C['instances with distinct tops'] += 1
            for v, (st, ex) in out.items():
                C[v + ': runs'] += st['runs']; C[v + ': runs stuck'] += st.get('stuck', 0)
                C[v + ': runs not EFX0'] += st.get('notefx0', 0)
                C[v + ': instances with a failing run'] += st.get('efx0', 0) < st['runs']
                C[v + ': instances with no EFX0 run'] += st.get('efx0', 0) == 0
                if st.get('efx0', 0) < st['runs']:
                    bad[v].append((n, m, sum(map(len, sets)), name, sets, vals, ex))
    for k in sorted(C): print('%-50s %d' % (k, C[k]))
    for v, L in bad.items():
        for n, m, s, name, sets, vals, ex in sorted(L)[:3]:
            print('  %s failing run: %s n=%d m=%d %s run %s' % (v, name, n, m, json.dumps({'sets': sets, 'vals': vals, 'm': m}), json.dumps(ex)[:300]))
    print('time %.0f s' % (time.time() - t0))
