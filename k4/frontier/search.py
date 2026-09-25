"""k = 4 frontier search: search4.py's CEGAR with a subsumption scanner (scan2.c) in place of scan.c.

Same cores (search4.cores), same type domains, same inner SAT model and safety masks (search4.Core), same certificate
format, so k4/check4.py checks the output unchanged. Only the proposal step differs: scan2.find returns a profile no
allocation found so far covers, or proves there is none, using minimal rows, full-safety sets and a store of covered
prefix sets (see scan2.c). The certificate does not depend on the scanner's correctness: check4.py re-checks coverage.

Usage: search.py n [--pure] [--n4=K] [--m=M[,M..]] [--part=i/k] [--jobs=J] [--cap=N] [--store=S] [--out=FILE] [--fresh]
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
LIB.ctx_new.argtypes = [ctypes.c_int, ctypes.c_int]
LIB.ctx_free.argtypes = [ctypes.c_void_p]
LIB.ctx_nodes.restype = ctypes.c_long
LIB.ctx_nodes.argtypes = [ctypes.c_void_p]
LIB.find.argtypes = [ctypes.c_void_p, ctypes.c_int] + [ctypes.c_void_p] * 2 + [ctypes.c_int] + [ctypes.c_void_p] * 4
STORE = 4096

def cegar(C, s, c, cap, tries=8, order=None, rand=1024):
    """As search4.Core.cegar: returns (allocations, failing profiles, complete?, stats)."""
    n = C.n
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
    ctx = LIB.ctx_new(n, STORE)
    rng = np.random.default_rng(12345)
    out = (ctypes.c_int * n)()
    ordc = (ctypes.c_int * n)(*order)
    domc = (ctypes.c_int * n)(*sizes.tolist())
    basec = (ctypes.c_long * n)(*base[:n].tolist())
    calls = 0
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
                if not LIB.find(ctx, n, ordc, domc, W, Mc.ctypes.data, basec, Fc.ctypes.data, out):
                    return allocs, fails, True, {'calls': calls, 'nodes': LIB.ctx_nodes(ctx)}
                prof = list(out)
            best = C.best_allocation(sol, x, z, prof, tries)
            if best is None:
                fails.append(prof)
                if len(fails) > cap: return allocs, fails, False, {'calls': calls, 'nodes': LIB.ctx_nodes(ctx)}
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
