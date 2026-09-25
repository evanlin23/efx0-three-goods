"""scan2.find against brute force: random row bitsets (2-5 agents, 1-40 types each, up to 300 allocations), columns
added one at a time with one persistent context (as in the CEGAR, so the covered-prefix store is exercised across
calls). Checks: find returns 1 iff some profile is uncovered, and the profile it returns is uncovered.
Usage: test_scan2.py [trials]"""
import ctypes, itertools, sys
import numpy as np
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
import search as FS

def brute(M, base, sizes, W):
    for prof in itertools.product(*[range(s) for s in sizes]):
        acc = np.full(W, ~np.uint64(0))
        for i, t in enumerate(prof): acc &= M[base[i] + t]
        if not acc.any(): return prof
    return None

def trial(rng, stats):
    n = int(rng.integers(2, 6))
    sizes = [int(rng.integers(1, 41 if n <= 3 else 12)) for _ in range(n)]
    base = np.cumsum([0] + sizes)
    K = int(rng.integers(1, 300)); Wmax = (K + 63) // 64
    dens = rng.uniform(0.3, 0.97)
    cols = rng.random((K, base[-1])) < dens
    order = list(rng.permutation(n))
    ctx = FS.LIB.ctx_new(n, int(rng.choice([0, 3, 50, 4096])), int(rng.integers(1, 4)))
    M = np.zeros((base[-1], Wmax), dtype=np.uint64)
    out = (ctypes.c_int * n)()
    for k in range(K):
        for r in np.flatnonzero(cols[k]): M[r, k // 64] |= np.uint64(1 << (k % 64))
        if rng.random() < 0.7 and k < K - 1: continue
        W = k // 64 + 1
        Mc = np.ascontiguousarray(M[:, :W])
        full = np.zeros((n, W), dtype=np.uint64)
        for i in range(n):
            full[i] = np.bitwise_and.reduce(Mc[base[i]:base[i + 1]], axis=0)
        F = np.zeros((n + 1, W), dtype=np.uint64); F[n] = ~np.uint64(0)
        for l in range(n - 1, -1, -1): F[l] = F[l + 1] & full[order[l]]
        f = FS.LIB.find(ctx, n, (ctypes.c_int * n)(*order), (ctypes.c_int * n)(*sizes), W, Mc.ctypes.data,
                        (ctypes.c_long * n)(*base[:n].tolist()), F.ctypes.data, out)
        b = brute(Mc, base, sizes, W)
        if bool(f) != (b is not None): return f"MISMATCH find={f} brute={b} n={n} sizes={sizes} K={k + 1}"
        if f:
            acc = np.full(W, ~np.uint64(0))
            for i, t in enumerate(out):
                if not 0 <= t < sizes[i]: return f"BAD PROFILE {list(out)}"
                acc &= Mc[base[i] + t]
            if acc.any(): return f"RETURNED A COVERED PROFILE {list(out)}"
        stats[bool(f)] += 1
    FS.LIB.ctx_free(ctx)
    return None

if __name__ == '__main__':
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    rng, stats = np.random.default_rng(2026), {True: 0, False: 0}
    for t in range(trials):
        err = trial(rng, stats)
        if err: print(f"trial {t}: {err}"); sys.exit(1)
    print(f"{trials} trials, {stats[True] + stats[False]} calls ({stats[True]} uncovered, {stats[False]} covered): all agree with brute force")
