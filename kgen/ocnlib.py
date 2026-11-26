"""Python side of kgen/ocn.c (OC1 brute force for n <= 5 agents, any k).

    from ocnlib import brute_n
    brute_n(v) -> (orders, per order dict NONE, CODE, STRICT, FREE0, FREEOC, MD, EFX, and picks)"""
import os, ctypes, itertools, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
KEYS = ['NONE', 'CODE', 'STRICT', 'FREE0', 'FREEOC', 'MD', 'EFX']
_lib = None


def lib():
    global _lib
    if _lib is None:
        so = os.path.join(HERE, 'libocn.so'); src = os.path.join(HERE, 'ocn.c')
        if not os.path.exists(so) or os.path.getmtime(so) < os.path.getmtime(src):
            tmp = so + '.%d.tmp' % os.getpid()
            subprocess.check_call(['gcc', '-O2', '-march=native', '-shared', '-fPIC', '-o', tmp, src]); os.replace(tmp, so)
        _lib = ctypes.CDLL(so)
        _lib.ocn.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.POINTER(ctypes.c_longlong),
                             ctypes.POINTER(ctypes.c_longlong), ctypes.POINTER(ctypes.c_int)]
    return _lib


def brute_n(v):
    n, m = len(v), len(v[0]); NP = 1
    for i in range(2, n + 1): NP *= i
    arr = (ctypes.c_longlong * (n * m))(*[int(x) for r in v for x in r])
    out = (ctypes.c_longlong * (8 * NP))(); pk = (ctypes.c_int * (n * NP))()
    lib().ocn(n, m, arr, out, pk)
    orders = list(itertools.permutations(range(n)))
    res = []
    for o in range(NP):
        d = {k: out[o * 8 + t] for t, k in enumerate(KEYS)}
        d['picks'] = [pk[o * n + i] if pk[o * n + i] >= 0 else None for i in range(n)]
        res.append(d)
    return orders, res
