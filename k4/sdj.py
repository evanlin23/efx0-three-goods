"""Does a serial-dictatorship-plus-junk construction (the shape of LB's output, proofs/construction.md §3) work at k = 4?

Model SDJ(s, c): some order of the agents; in that order each agent picks its favourite remaining good (nothing if
none of its goods remains); the unpicked goods (junk) are placed arbitrarily, with at most c bundles of more than s
goods (s = None: no limit). LB and LB's upgrades produce allocations of this shape (LB's order is adaptive, so SDJ
failing implies LB failing; LB⁺'s rotation leaves the shape and is not covered).
CEGAR as in search4.py: for a proposed profile, try every order (n!), fix the picks and let SAT place the junk;
the box an allocation covers is, per agent, the types under which it is safe AND whose ranking makes the same pick.
Usage: sdj.py n [--pure] [--s=2] [--c=1] [--cap=N] [--jobs=J] [--log-fails=K] [--sample=R (random profiles, EVIDENCE)]"""
import ctypes, itertools, os, sys, time
from multiprocessing import Pool
import numpy as np
import search4 as S4

def picks(C, order, prof):
    taken, pick = set(), {}
    for i in order:
        v = C.dom[i][prof[i]]
        left = [p for p, g in enumerate(C.sets[i]) if g not in taken]
        if left:
            p = max(left, key=lambda p: v[p]); pick[i] = C.sets[i][p]; taken.add(pick[i])
    return pick

def consistent(C, order, pick):
    """Per agent, bitmask of its types that make the same pick in this order (depends on the ranking only)."""
    masks, taken = [0] * C.n, set()
    for i in order:
        left = [p for p, g in enumerate(C.sets[i]) if g not in taken]
        for t, v in enumerate(C.dom[i]):
            if not left: ok = i not in pick
            else: ok = i in pick and C.sets[i][max(left, key=lambda p: v[p])] == pick[i]
            if ok: masks[i] |= 1 << t
        if i in pick: taken.add(pick[i])
    return masks

def cegar_sdj(C, s, c, cap):
    n = C.n
    dom = (ctypes.c_int * n)(*[len(D) for D in C.dom])
    base = np.cumsum([0] + [len(D) for D in C.dom])
    cbase = (ctypes.c_long * n)(*base[:n].tolist())
    M, ncol = np.zeros((base[-1], 16), dtype=np.uint64), 0
    def add(masks):
        nonlocal M, ncol
        if ncol == 64 * M.shape[1]: M = np.concatenate([M, np.zeros_like(M)], axis=1)
        for i in range(n):
            ts = [t for t in range(len(C.dom[i])) if masks[i] >> t & 1]
            M[base[i] + np.array(ts, dtype=np.int64), ncol // 64] |= np.uint64(1 << (ncol % 64))
        ncol += 1
    sol, x, z = C.inner(s, c)
    start, out = (ctypes.c_int * n)(*([0] * n)), (ctypes.c_int * n)()
    nalloc, fails = 0, []
    while True:
        W = max(1, (ncol + 63) // 64)
        Mc = np.ascontiguousarray(M[:, :W])
        if not S4.SCAN.scan(n, dom, W, Mc.ctypes.data_as(ctypes.POINTER(ctypes.c_uint64)), cbase, start, out):
            return nalloc, fails, True
        prof = list(out)
        for i in range(n): start[i] = prof[i]
        best = None
        for order in itertools.permutations(range(n)):
            pick = picks(C, order, prof)
            assum = [z[i][t] for i, t in enumerate(prof)] + [x[g][i] for i, g in pick.items()]
            if not sol.solve(assumptions=assum): continue
            mod = set(l for l in sol.get_model() if l > 0)
            A = [next(j for j in range(n) if x[g][j] in mod) for g in range(C.m)]
            cons = consistent(C, order, pick)
            masks = [C.safe_mask(i, A) & cons[i] for i in range(n)]
            vol = sum(np.log(max(1, bin(mk).count('1'))) for mk in masks)
            if best is None or vol > best[0]: best = (vol, masks)
        if best is None:
            fails.append(prof)
            if len(fails) > cap: return nalloc, fails, False
            add([1 << t for t in prof])
        else:
            nalloc += 1; add(best[1])

def sdj_exists(C, sol, x, z, prof):
    """Is there an order whose picks, plus some junk placement allowed by the solver's shape, give an EFX₀ allocation?"""
    for order in itertools.permutations(range(C.n)):
        pick = picks(C, order, prof)
        if sol.solve(assumptions=[z[i][t] for i, t in enumerate(prof)] + [x[g][i] for i, g in pick.items()]):
            return order
    return None

def sample(task):
    n, m, idx, sets, s, c, R, seed = task
    import random
    C, rng = S4.Core(n, m, sets), random.Random(seed)
    sol, x, z = C.inner(s, c)
    fails = []
    for _ in range(R):
        prof = [rng.randrange(len(D)) for D in C.dom]
        if sdj_exists(C, sol, x, z, prof) is None: fails.append([list(C.dom[i][t]) for i, t in enumerate(prof)])
    return m, sets, fails

def solve(task):
    n, m, idx, sets, s, c, cap = task
    C, t0 = S4.Core(n, m, sets), time.time()
    nalloc, fails, complete = cegar_sdj(C, s, c, cap)
    out = []
    for prof in fails[:5]:
        sol, x, z = C.inner(None, None)
        out.append({'profile': [list(C.dom[i][t]) for i, t in enumerate(prof)],
                    'efx0': C.allocation(sol, x, z, prof) is not None,
                    'min_big2': C.min_big(prof, 2)})
    return {'n': n, 'm': m, 'idx': idx, 'sets': sets, 'allocs': nalloc,
            'fails': len(fails) if complete else f'>{cap}', 'examples': out, 'time': round(time.time() - t0, 1)}

if __name__ == '__main__':
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in sys.argv[1:] if a.startswith('--'))
    pure, cap, jobs = 'pure' in opt, int(opt.get('cap', 1000)), int(opt.get('jobs', os.cpu_count()))
    s = None if opt.get('s', '2') == 'none' else int(opt.get('s', 2))
    c = int(opt.get('c', 1))
    if 'sample' in opt:
        R = int(opt['sample'])
        for n in map(int, args):
            tasks = [(n, m, idx, sets, s, c, R, hash((m, idx)) & 0xffff) for m in range(4, 3 * n + 1)
                     for idx, sets in enumerate(S4.cores(n, m, pure))]
            print(f"SDJ(s={s}, c={c}) n={n}{' pure' if pure else ''}: {len(tasks)} cores x {R} random strict profiles", flush=True)
            t0, per_m, shown = time.time(), {}, 0
            with Pool(jobs) as pool:
                for m, sets, fails in pool.imap_unordered(sample, tasks):
                    st = per_m.setdefault(m, [0, 0, 0]); st[0] += 1; st[1] += bool(fails); st[2] += len(fails)
                    if fails and shown < int(opt.get('log-fails', 3)):
                        shown += 1; print(f"  fails: m={m} sets={sets} ({len(fails)}/{R}); e.g. {fails[0]}", flush=True)
            for m, st in sorted(per_m.items()):
                print(f"  m={m}: {st[0]} cores; SDJ fails in {st[1]} cores, on {st[2]} of {st[0] * R} sampled profiles", flush=True)
            print(f"  [{time.time() - t0:.0f}s]", flush=True)
        sys.exit(0)
    for n in map(int, args):
        tasks = [(n, m, idx, sets, s, c, cap) for m in range(4, 3 * n + 1)
                 for idx, sets in enumerate(S4.cores(n, m, pure))]
        print(f"SDJ(s={s}, c={c}) n={n}{' pure' if pure else ''}: {len(tasks)} cores", flush=True)
        t0, res = time.time(), []
        with Pool(jobs) as pool:
            for r in pool.imap_unordered(solve, tasks): res.append(r)
        res.sort(key=lambda r: (r['m'], r['idx']))
        for m in sorted({r['m'] for r in res}):
            R = [r for r in res if r['m'] == m]
            print(f"  m={m}: {len(R)} cores, SDJ fails in {sum(r['fails'] != 0 for r in R)}", flush=True)
        bad = [r for r in res if r['fails'] != 0]
        for r in bad[:int(opt.get('log-fails', 3))]:
            print(f"  fails: m={r['m']} sets={r['sets']} failing profiles={r['fails']}; e.g. {r['examples'][0]}", flush=True)
        print(f"  [{time.time() - t0:.0f}s]", flush=True)
