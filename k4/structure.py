"""Structure statistics for k = 4 cores (plan Step 2 analogue), exhaustive over strict profiles by CEGAR (search4.py):
  C2: all bundles <= 2 goods (possible only if m <= 2n);  C3: all bundles <= 3 goods;
  L:  the least L such that every profile has an EFX₀ allocation with at most one bundle of more than 2 goods and
      that bundle of at most L goods (counting lower bound: max(3, m - 2n + 2) when m > 2n, else 3 if C2 fails).
For each core: C2 / C3 hold for every profile, or the first failing profile found. Usage: structure.py n [--pure] [--jobs=J] [--out=FILE.json]"""
import os, sys, time
from multiprocessing import Pool
import search4 as S4

def run(task):
    n, m, idx, sets = task
    C, t0 = S4.Core(n, m, sets), time.time()
    rec = {'m': m, 'sets': sets}
    for name, s, c in (('C2', 2, 0), ('C3', 3, 0)):
        if s * n < m: rec[name] = 'impossible'; continue
        allocs, fails, complete = C.cegar(s, c, 0)
        rec[name] = 'holds' if complete and not fails else [list(C.dom[i][t]) for i, t in enumerate(fails[0])]
    lb = max(3, m - 2 * n + 2)
    L = lb
    while True:
        allocs, fails, complete = C.cegar(2, 1, 0, maxsize=L)
        if complete and not fails: break
        rec['L_fail'] = [list(C.dom[i][t]) for i, t in enumerate(fails[0])]   # fails with the large bundle <= L
        L += 1
    rec['L'], rec['L_lb'], rec['time'] = L, lb, round(time.time() - t0, 1)
    return rec

if __name__ == '__main__':
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in sys.argv[1:] if a.startswith('--'))
    n, pure = int(args[0]), 'pure' in opt
    tasks = [(n, m, idx, sets) for m in range(4, 3 * n + 1) for idx, sets in enumerate(S4.cores(n, m, pure))]
    print(f"structure n={n}{' pure' if pure else ''}: {len(tasks)} cores", flush=True)
    t0, res = time.time(), []
    with Pool(int(opt.get('jobs', os.cpu_count()))) as pool:
        for r in pool.imap_unordered(run, tasks): res.append(r)
    for m in sorted({r['m'] for r in res}):
        R = [r for r in res if r['m'] == m]
        cnt = lambda k: {v: sum(1 for r in R if (r[k] if isinstance(r[k], str) else 'fails') == v) for v in ('holds', 'fails', 'impossible')}
        Ls = {}
        for r in R: Ls[(r['L'], r['L_lb'])] = Ls.get((r['L'], r['L_lb']), 0) + 1
        print(f"  m={m}: {len(R)} cores; C2 {cnt('C2')}; C3 {cnt('C3')}; (L, lower bound): count {Ls}", flush=True)
    for key in ('C2', 'C3'):
        ex = sorted((r for r in res if isinstance(r[key], list)), key=lambda r: r['m'])
        if ex: print(f"  smallest {key} failure: m={ex[0]['m']} sets={ex[0]['sets']} profile={ex[0][key]}", flush=True)
    ex = sorted((r for r in res if r['L'] > r['L_lb']), key=lambda r: r['m'])
    if ex: print(f"  large bundle above the lower bound: m={ex[0]['m']} sets={ex[0]['sets']} L={ex[0]['L']} "
                 f"(bound {ex[0]['L_lb']}), profile={ex[0]['L_fail']}", flush=True)
    print(f"  [{time.time() - t0:.0f}s]", flush=True)
    if 'out' in opt:
        import json
        json.dump(sorted(res, key=lambda r: (r['m'], r['sets'])), open(opt['out'], 'w'), separators=(',', ':'))
