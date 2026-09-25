"""k = 4 frontier search: search4.py's CEGAR with a subsumption scanner (scan2.c) in place of scan.c.

Same cores (search4.cores), same type domains, same inner SAT model and safety masks (search4.Core), same certificate
format, so k4/check4.py checks the output unchanged. Only the proposal step differs: scan2.find returns a profile no
allocation found so far covers, or proves there is none, using minimal rows, full-safety sets and a store of covered
prefix sets (see scan2.c). The certificate does not depend on the scanner's correctness: check4.py re-checks coverage.

Usage: search.py n [--pure] [--n4=K] [--m=M[,M..]] [--part=i/k] [--jobs=J] [--cap=N] [--tries=T] [--out=FILE] [--fresh]
  --tries: SAT solutions tried per proposal (best covered box kept; default 8, as search4.py);
  --m: only these m; --part=i/k: only cores with index ≡ i (mod k) in the (m, idx) list (for splitting long runs);
  checkpoint k4/frontier/checkpoint_<tag>.jsonl (resume by rerunning)."""
import ctypes, gzip, json, os, subprocess, sys, time
import numpy as np
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import search4 as S4

_so = os.path.join(HERE, 'scan2.so')
if not os.path.exists(_so) or os.path.getmtime(_so) < os.path.getmtime(os.path.join(HERE, 'scan2.c')):
    subprocess.run(['gcc', '-O2', '-shared', '-fPIC', '-o', _so, os.path.join(HERE, 'scan2.c')], check=True)
LIB = ctypes.CDLL(_so)
LIB.ctx_new.restype = ctypes.c_void_p
LIB.ctx_new.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_int]
LIB.ctx_free.argtypes = [ctypes.c_void_p]
LIB.ctx_nodes.restype = ctypes.c_long
LIB.ctx_nodes.argtypes = [ctypes.c_void_p]
LIB.find.argtypes = [ctypes.c_void_p, ctypes.c_int] + [ctypes.c_void_p] * 2 + [ctypes.c_int] + [ctypes.c_void_p] * 4
STORE, DEPTH, TRIES = 100000, 2, 8                       # store size per level; no store at the last DEPTH levels

def cegar(C, s, c, cap, tries=None, order=None, rand=1024):
    """As search4.Core.cegar: returns (allocations, failing profiles, complete?, stats)."""
    n = C.n
    if tries is None: tries = TRIES
    sizes = np.array([len(D) for D in C.dom])
    if order is None: order = sorted(range(n), key=lambda i: (-sizes[i], i))
    base = np.cumsum([0] + sizes.tolist())
    Wmax = 16
    M = np.zeros((base[-1], Wmax), dtype=np.uint64)
    full_rows = np.zeros((n, Wmax), dtype=np.uint64)      # agent i safe with every type
    ncol = 0
    def add(masks):
        nonlocal M, full_rows, ncol, Wmax
        if ncol == 64 * Wmax:
            M = np.concatenate([M, np.zeros_like(M)], axis=1)
            full_rows = np.concatenate([full_rows, np.zeros_like(full_rows)], axis=1); Wmax *= 2
        bit = np.uint64(1 << (ncol % 64))
        for i in range(n):
            ts = [t for t in range(sizes[i]) if masks[i] >> t & 1]
            M[base[i] + np.array(ts, dtype=np.int64), ncol // 64] |= bit
            if len(ts) == sizes[i]: full_rows[i, ncol // 64] |= bit
        ncol += 1
    sol, x, z = C.inner(s, c)
    allocs, fails = [], []
    ctx = LIB.ctx_new(n, STORE, DEPTH)
    rng = np.random.default_rng(12345)
    out = (ctypes.c_int * n)()
    ordc = (ctypes.c_int * n)(*order)
    domc = (ctypes.c_int * n)(*sizes.tolist())
    basec = (ctypes.c_long * n)(*base[:n].tolist())
    calls, tscan = 0, 0.0
    try:
        while True:
            W = max(1, (ncol + 63) // 64)
            prof = None
            if rand and ncol < 64 * 8:                     # cheap random proposals while few allocations exist
                P = rng.integers(0, sizes, size=(rand, n))
                acc = np.full((rand, W), ~np.uint64(0))
                for i in range(n): acc &= M[base[i] + P[:, i], :W]
                unc = np.flatnonzero(~acc.any(axis=1))
                if len(unc): prof = P[unc[0]].tolist()
                else: rand = 0
            if prof is None:
                Mc = np.ascontiguousarray(M[:, :W])
                Fc = np.zeros((n + 1, W), dtype=np.uint64)
                Fc[n] = ~np.uint64(0)
                for l in range(n - 1, -1, -1): Fc[l] = Fc[l + 1] & full_rows[order[l], :W]
                calls += 1
                t0 = time.time()
                found = LIB.find(ctx, n, ordc, domc, W, Mc.ctypes.data, basec, Fc.ctypes.data, out)
                tscan += time.time() - t0
                if not found:
                    return allocs, fails, True, {'calls': calls, 'nodes': LIB.ctx_nodes(ctx), 'scan_s': round(tscan, 2)}
                prof = list(out)
            best = C.best_allocation(sol, x, z, prof, tries)
            if best is None:
                fails.append(prof)
                if len(fails) > cap: return allocs, fails, False, {'calls': calls, 'nodes': LIB.ctx_nodes(ctx), 'scan_s': round(tscan, 2)}
                add([1 << t for t in prof])
                continue
            allocs.append(best[0])
            add(best[1])
    finally:
        LIB.ctx_free(ctx)

def solve(task):
    """As search4.solve, with the new cegar."""
    n, m, idx, sets, cap = task
    C, t0 = S4.Core(n, m, sets), time.time()
    rec = {'n': n, 'm': m, 'idx': idx, 'sets': sets, 'domains': [len(D) for D in C.dom]}
    allocs, fails, complete, st = cegar(C, 2, 1, cap)
    rec['D2_fails'] = len(fails) if complete else f'>{cap}'
    model_used = 'D2'
    if not complete:
        allocs, fails, complete, st = cegar(C, 3, 1, cap)
        rec['D3_fails'] = len(fails) if complete else f'>{cap}'
        model_used = 'D3'
        if not complete:
            allocs, fails, complete, st = cegar(C, None, None, cap)
            model_used = 'ANY'
    rec['model'], rec['fail_profiles'] = model_used, []
    for prof in fails:
        sol, x, z = C.inner(None, None)
        A = C.allocation(sol, x, z, prof)
        info = {'profile': [list(C.dom[i][t]) for i, t in enumerate(prof)], 'efx0': A is not None}
        if A is not None:
            info['min_big2'], info['min_big3'] = C.min_big(prof, 2), C.min_big(prof, 3)
            sol, x, z = C.inner(3, info['min_big3'])
            A = C.allocation(sol, x, z, prof)
            info['alloc'] = A
            allocs.append(A)
        rec['fail_profiles'].append(info)
    rec['counterexample'] = any(not f['efx0'] for f in rec['fail_profiles']) or not complete
    rec['allocs'] = allocs
    rec['scan'] = st
    rec['time'] = round(time.time() - t0, 2)
    return rec

def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in sys.argv[1:] if a.startswith('--'))
    pure, cap, jobs = 'pure' in opt, int(opt.get('cap', 20)), int(opt.get('jobs', os.cpu_count()))
    n4 = int(opt['n4']) if 'n4' in opt else None
    ms = set(map(int, opt['m'].split(','))) if 'm' in opt else None
    part, parts = map(int, opt.get('part', '0/1').split('/'))
    n = int(args[0])
    global TRIES
    TRIES = int(opt.get('tries', TRIES))
    print("command: python3 k4/frontier/search.py " + ' '.join(sys.argv[1:]), flush=True)
    t0 = time.time()
    tasks = [(n, m, idx, sets, cap) for m in range(4, 3 * n + 1) for idx, sets in enumerate(S4.cores(n, m, pure, n4))]
    total = len(tasks)
    tag = f"{n}{'_pure' if pure else ''}{'' if n4 is None else f'_n4_{n4}'}"
    ckpts = sorted(f for f in os.listdir(HERE) if f.startswith(f'checkpoint_{tag}_') and f.endswith('.jsonl'))
    done = {}
    for fn in ([] if 'fresh' in opt else ckpts):
        for line in open(os.path.join(HERE, fn)):
            try: r = json.loads(line)
            except json.JSONDecodeError: continue                       # a line cut by a killed run
            done[(r['m'], r['idx'])] = r
    mine = [t for k, t in enumerate(tasks) if k % parts == part and (ms is None or t[1] in ms)]
    todo = [t for t in mine if (t[1], t[2]) not in done]
    print(f"n={n} ({'pure' if pure else 'degrees 3-4'}{'' if n4 is None else f', exactly {n4} of degree 4'}): {total} cores;"
          f" this part: {len(mine)}, already done: {len(mine) - len(todo)} (checkpoints {ckpts})", flush=True)
    ck = os.path.join(HERE, f"checkpoint_{tag}_{opt.get('m', 'all').replace(',', '-')}_p{part}of{parts}.jsonl")
    stats, cnt = {}, 0
    with Pool(jobs) as pool, open(ck, 'a') as f:
        for rec in pool.imap_unordered(solve, todo, chunksize=1):
            f.write(json.dumps(rec, separators=(',', ':')) + '\n'); f.flush()
            done[(rec['m'], rec['idx'])] = rec; cnt += 1
            if rec['counterexample']: print("  COUNTEREXAMPLE CANDIDATE", rec['sets'], rec['fail_profiles'][:1], flush=True)
            if rec['D2_fails'] != 0: print(f"  D2 fails: m={rec['m']} sets={rec['sets']} ({rec['D2_fails']} profiles)", flush=True)
            if cnt % 100 == 0: print(f"  ... {cnt}/{len(todo)} [{time.time() - t0:.0f}s]", flush=True)
    for (m, idx), r in done.items():
        st = stats.setdefault(m, {'cores': 0, 'D2 fails': 0, 'cex': 0, 'allocs': 0, 'max allocs': 0, 'max s': 0})
        st['cores'] += 1; st['allocs'] += len(r['allocs']); st['D2 fails'] += r['D2_fails'] != 0
        st['cex'] += r['counterexample']; st['max allocs'] = max(st['max allocs'], len(r['allocs'])); st['max s'] = max(st['max s'], r['time'])
    for m, st in sorted(stats.items()): print(f"  m={m}: {st}", flush=True)
    print(f"  done {len(done)}/{total} cores [{time.time() - t0:.0f}s]", flush=True)
    if len(done) == total and all((t[1], t[2]) in done for t in tasks):
        path = opt.get('out', os.path.join(HERE, f"k4_certs_{tag}.json.gz"))
        out = [done[(t[1], t[2])] for t in tasks]
        with gzip.open(path, 'wt') as f:
            json.dump({'n': n, 'pure': pure, 'ties': False, 'n4': n4, 'cores': out}, f, separators=(',', ':'))
        print(f"  all cores done: wrote {path}", flush=True)
    else:
        print("  not all cores done yet: no certificate written (rerun the remaining parts)", flush=True)

if __name__ == '__main__':
    main()
