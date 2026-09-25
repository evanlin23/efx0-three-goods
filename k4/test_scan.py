"""Unit test of k4/scan.c against brute force on random bitset instances with several 64-bit words per row (the
case a row-offset bug once broke: masks are indexed (base[i] + t) * W). Usage: test_scan.py"""
import ctypes, itertools
import numpy as np
import search4 as S4

rng = np.random.default_rng(5)
for trial in range(30):
    n = 3; D = [int(x) for x in rng.integers(3, 8, n)]; K = int(rng.integers(65, 300)); W = (K + 63) // 64
    base = np.cumsum([0] + D)
    bits = rng.random((base[-1], K)) < rng.uniform(0.3, 0.9)
    M = np.zeros((base[-1], W), dtype=np.uint64)
    for r, a in zip(*np.nonzero(bits)): M[r, a // 64] |= np.uint64(1 << (int(a) % 64))
    F = np.zeros((n + 1, W), dtype=np.uint64)
    for a in range(K):
        for l in range(n + 1):
            if all(bits[base[j] + t, a] for j in range(l, n) for t in range(D[j])): F[l, a // 64] |= np.uint64(1 << (a % 64))
    brute = next((list(p) for p in itertools.product(*[range(d) for d in D])
                  if not any(all(bits[base[i] + p[i], a] for i in range(n)) for a in range(K))), None)
    start, out = (ctypes.c_int * n)(0, 0, 0), (ctypes.c_int * n)()
    r = S4.SCAN.scan(n, (ctypes.c_int * n)(*D), W, M.ctypes.data_as(ctypes.POINTER(ctypes.c_uint64)),
                     (ctypes.c_long * n)(*base[:n].tolist()), start, out, F.ctypes.data_as(ctypes.POINTER(ctypes.c_uint64)))
    got = list(out) if r else None
    assert got == brute, (trial, got, brute)
print('scan agrees with brute force on 30 random instances (W = 2..5)')
