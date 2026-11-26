"""Minimal-counterexample candidates with exactly n agents, every beta, from k4/mincex_shapes.py's generator.

A minimal counterexample to TARGET₄ has β ≥ 5 (K4.MC7) and is a connected k = 4 core satisfying K4.MC2, K4.MC3 and
K4.MC5 (k4/MINCEX.md). mincex_shapes.py lists, for one β, the graphs G' (private goods deleted) with genbg, applies the
structural filters and cuts each agent's type domain by the px profiles no reduction covers. Here: n fixed, every β
from BMIN to the largest one possible with n agents, isomorphic cores merged (per β they differ in m anyway).
Domains are not stored (run_mc.py recomputes them with mincex_shapes.restricted_domains); one file per beta,
OUT_b<beta>.json.gz.
Usage: mc_n.py N [--bmin=5] [--bmax=B] --write=OUT.json.gz"""
import sys, os, json, gzip, collections, pickle
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); K4 = os.path.dirname(HERE)
sys.path.insert(0, K4)
os.chdir(K4)
import mincex_shapes as MS

def main():
    n = int(sys.argv[1])
    opt = dict(a[2:].split('=', 1) for a in sys.argv[2:] if a.startswith('--') and '=' in a)
    bmin = int(opt.get('bmin', 5)); bmax = int(opt.get('bmax', 3 * n - 2))
    cache = os.path.join(HERE, 'ckpt', 'px_uncovered.pkl')
    if os.path.exists(cache): fail = pickle.load(open(cache, 'rb'))
    else:
        fail = MS.px_uncovered(); os.makedirs(os.path.dirname(cache), exist_ok=True); pickle.dump(fail, open(cache, 'wb'))
    for key, fs in sorted(fail.items()): print('px %s %s: %d profiles not reduced' % (key[0], 'closed' if key[1] else 'open', len(fs)), flush=True)
    orig = MS.gammas
    MS.gammas = lambda beta, nmin=5, nmax=None: orig(beta, nmin=n, nmax=n)
    total = 0
    for beta in range(bmin, bmax + 1):
        stat, recs = collections.Counter(), []
        for nn, m, sets in MS.hypergraphs(beta, n):
            stat[m] += 1
            dom, kinds, rules = MS.restricted_domains(sets, m, fail)
            size = int(np.prod([len(d) for d in dom], dtype=object))
            if size == 0: continue
            recs.append({'n': nn, 'm': m, 'beta': beta, 'sets': sets, 'kinds': kinds, 'profiles': size,
                         'dsizes': [len(d) for d in dom]})
        uniq = MS.unique([(r['n'], r['m'], r['sets']) for r in recs])
        keep = set(json.dumps(s) for _, _, s in uniq)
        recs = [r for r in recs if json.dumps(r['sets']) in keep]
        for m in sorted(stat):
            left = [r['profiles'] for r in recs if r['m'] == m]
            print(f"beta={beta} n={n} m={m}: {stat[m]} listed, {len(left)} left (profiles max {max(left) if left else 0}, "
                  f"total {sum(left)})", flush=True)
        total += len(recs)
        with gzip.open(opt['write'].replace('.json.gz', f'_b{beta}.json.gz'), 'wt') as f: json.dump(recs, f)
    print(f'total: {total} candidate cores', flush=True)

if __name__ == '__main__':
    main()
