"""Adversarial climb against PD (P1, k4/sdc.md §1) at n = 3: minimize the least number of complete EFX0 allocations
that value-dominate some partial EFX0 allocation (kgen/pd3.c, pd3_min).  0 = PD refuted: the instance is printed with
the undominated partial allocation and replayed by pd3_hunt.verify (pure Python) when m <= 10.

    [CLIMB_K=4] [CLIMB_STRICT=1] python3 kgen/pd3_climb.py SEED ROUNDS STEPS MMIN MMAX"""
import sys, os, ctypes, random, json, time, multiprocessing as mp
import climb3
from gen3 import gen
from pd3_hunt import lib, verify


def objective(v):
    m = len(v[0]); arr = (ctypes.c_longlong * (3 * m))(*[x for r in v for x in r]); arg = (ctypes.c_int * 4)()
    L = lib(); L.pd3_min.restype = ctypes.c_longlong
    L.pd3_min.argtypes = [ctypes.c_int, ctypes.POINTER(ctypes.c_longlong), ctypes.POINTER(ctypes.c_int)]
    best = L.pd3_min(m, arr, arg)
    return best, ([[g for g in range(m) if arg[k] >> g & 1] for k in range(4)] if arg[0] >= 0 else None)


def run_round(args):
    seed, steps, lo, hi = args
    rng = random.Random(seed)
    k = 'klim:%d' % climb3.KCAP if climb3.KCAP else rng.choice(['general', 'zeros', 'ident', 'junk', 'klim:4', 'klim:6'])
    m = rng.randint(lo, hi)
    if k.startswith('klim'): m = min(m, 3 * int(k.split(':')[1]))
    v = gen(k, m, rng); c, X = objective(v); best = c; found = None
    for s in range(steps):
        w = climb3.mutate(v, rng, lo, hi)
        if w is None: continue
        c2, X2 = objective(w)
        if c2 <= c or rng.random() < 0.02:
            v, c, X = w, c2, X2; best = min(best, c)
            if c == 0: found = (v, X); break
    return seed, k, c, best, v, found


if __name__ == '__main__':
    seed, rounds, steps, lo, hi = map(int, sys.argv[1:6])
    print('$ python3 kgen/pd3_climb.py', *sys.argv[1:], 'CLIMB_K=%d' % climb3.KCAP, flush=True); t0 = time.time()
    with mp.Pool(os.cpu_count()) as pool:
        for s, k, c, best, v, found in pool.imap_unordered(run_round, [(seed * 7919 + t, steps, lo, hi) for t in range(rounds)]):
            if found:
                ok = verify(found[0], found[1]) if len(v[0]) <= 10 else 'not replayed'
                print('PD FAILS', json.dumps(found[0]), 'undominated partial', found[1][:3], 'unallocated', found[1][3],
                      'replay', ok, flush=True)
            print('round seed', s, 'start', k, 'final', c, 'best', best, 'm', len(v[0]), 'inst', json.dumps(v),
                  'time %.0f' % (time.time() - t0), flush=True)
