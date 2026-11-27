"""Hunt for partial EFX0 allocations that no complete EFX0 allocation value-dominates (PD = P1 of k4/sdc.md §1), three
agents, any k, brute force (kgen/pd3.c).  Prints every refuting instance with one undominated partial allocation, and
re-verifies it with an independent pure-Python brute force (all 3^m complete allocations, raw EFX0 definition).

    python3 kgen/pd3_hunt.py SEED N MMIN MMAX [kinds]"""
import sys, os, ctypes, random, json, time, itertools, collections, subprocess, multiprocessing as mp
from gen3 import gen

HERE = os.path.dirname(os.path.abspath(__file__))
_lib = None


def lib():
    global _lib
    if _lib is None:
        so = os.path.join(HERE, 'libpd3.so'); src = os.path.join(HERE, 'pd3.c')
        if not os.path.exists(so) or os.path.getmtime(so) < os.path.getmtime(src):
            tmp = so + '.%d.tmp' % os.getpid()
            subprocess.check_call(['gcc', '-O2', '-march=native', '-shared', '-fPIC', '-o', tmp, src]); os.replace(tmp, so)
        _lib = ctypes.CDLL(so)
        _lib.pd3.restype = ctypes.c_longlong
        _lib.pd3.argtypes = [ctypes.c_int, ctypes.POINTER(ctypes.c_longlong), ctypes.POINTER(ctypes.c_int)]
    return _lib


def pd(v):
    m = len(v[0]); arr = (ctypes.c_longlong * (3 * m))(*[x for r in v for x in r]); bad = (ctypes.c_int * 4)()
    nb = lib().pd3(m, arr, bad)
    cnt = (ctypes.c_longlong * 2).in_dll(lib(), 'pd3_count')
    X = None if bad[0] < 0 else [[g for g in range(m) if bad[k] >> g & 1] for k in range(4)]
    return nb, X, (cnt[0], cnt[1])


def efx0(v, X):
    for i in range(3):
        own = sum(v[i][g] for g in X[i])
        for j in range(3):
            if j != i and len(X[j]) >= 2 and sum(v[i][g] for g in X[j]) - min(v[i][g] for g in X[j]) > own:
                return False
    return True


def verify(v, X):
    """independent check: X (3 bundles, rest unallocated) is partial EFX0 and no complete EFX0 allocation dominates"""
    m = len(v[0])
    if not efx0(v, X[:3]): return False
    u = [sum(v[i][g] for g in X[i]) for i in range(3)]
    for asg in itertools.product(range(3), repeat=m):
        B = [[g for g in range(m) if asg[g] == i] for i in range(3)]
        if all(sum(v[i][g] for g in B[i]) >= u[i] for i in range(3)) and efx0(v, B): return False
    return True


def job(args):
    seed, kind, m = args
    if kind.startswith('klim'): m = min(m, 3 * int(kind.split(':')[1]))
    rng = random.Random(seed); v = gen(kind, m, rng); nb, X, cnt = pd(v)
    return kind, m, v, nb, X, cnt


if __name__ == '__main__':
    seed, N, lo, hi = map(int, sys.argv[1:5])
    kinds = sys.argv[5].split(',') if len(sys.argv) > 5 else ['general', 'zeros', 'ident', 'junk', 'klim:3', 'klim:4', 'klim:6', 'ties']
    print('$ python3 kgen/pd3_hunt.py', *sys.argv[1:], flush=True); t0 = time.time()
    rng = random.Random(seed); C = collections.Counter()
    tasks = [(seed * 1000003 + t, kinds[t % len(kinds)], rng.randint(lo, hi)) for t in range(N)]
    with mp.Pool(os.cpu_count()) as pool:
        for kind, m, v, nb, X, cnt in pool.imap_unordered(job, tasks, chunksize=4):
            C['instances %s' % kind] += 1
            if nb:
                C['PD FAILS %s' % kind] += 1
                ok = verify(v, X) if m <= 10 else 'not replayed (m > 10)'
                print('PD FAILS', kind, 'm', m, json.dumps(v), 'undominated partial', X[:3], 'unallocated', X[3],
                      'count', nb, 'replay', ok, flush=True)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
