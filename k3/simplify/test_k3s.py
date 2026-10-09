"""Tests of K3S (k3s.py) against the raw EFX0 definition. Evidence only.
  cores N        : every ranking profile of every certified core with n <= N, three balanced realizations
  small N M      : every ranking profile with n = N agents on M goods (unranked goods are worthless; agent 0 ranks
                   0 > 1 > 2 by symmetry), values 4, 3, 2
  random K SEED  : K random general instances (0-3 goods per agent, values 1..6: ties, top-heavy, a = b + c, ...)
  sd2 K SEED     : K random instances with <= 2 goods per agent: K3S == serial dictatorship + last agent absorbs"""
import sys, os, random, itertools, collections, multiprocessing
sys.path.insert(0, os.path.dirname(__file__))
from k3s import k3s, efx0
from lbx import core_profiles
REAL = [(4, 3, 2), (10, 9, 2), (10, 6, 5)]

def w_core(a):
    n, m, rank = a
    bad = []
    for real in REAL:
        v = [dict(zip(r, real)) for r in rank]; info = {}
        if not efx0(n, m, v, k3s(n, m, v, info)): bad.append((rank, m, real))
    return n, bad, info.get('branch')

def w_small(a):
    n, m, rank = a
    v = [dict(zip(r, REAL[0])) for r in rank]; info = {}
    return n, ([] if efx0(n, m, v, k3s(n, m, v, info)) else [(rank, m)]), info.get('branch')

def gen_small(n, m):
    tri = list(itertools.permutations(range(m), 3))
    for rest in itertools.product(tri, repeat=n - 1):
        yield n, m, [(0, 1, 2)] + list(rest)

def rand_inst(rng, maxk=3):
    n = rng.randint(1, 9); m = rng.randint(0, 2 * n + 4)
    v = []
    for i in range(n):
        k = rng.randint(0, min(maxk, m)) if rng.random() < 0.3 else min(maxk, m)
        gs = rng.sample(range(m), k)
        v.append({g: rng.randint(1, 6) for g in gs})
    return n, m, v

def w_rand(a):
    seed, K = a
    rng = random.Random(seed); bad = []; br = collections.Counter()
    for _ in range(K):
        n, m, v = rand_inst(rng); info = {}
        X = k3s(n, m, v, info); br[info.get('branch')] += 1
        if not efx0(n, m, v, X): bad.append((n, m, v))
    return bad, br

def w_rprof(a):
    seed, K = a
    rng = random.Random(seed); bad = []; br = collections.Counter()
    for _ in range(K):
        n = rng.randint(2, 9); m = rng.randint(max(3, n), 2 * n + 3); real = rng.choice(REAL)
        v = [dict(zip(rng.sample(range(m), 3), real)) for _ in range(n)]; info = {}
        X = k3s(n, m, v, info); br[info.get('branch')] += 1
        if not efx0(n, m, v, X): bad.append((n, m, v))
    return bad, br

def sd2(n, m, v):
    rk = [sorted(v[i], key=lambda g: (-v[i][g], g)) for i in range(n)]
    free = set(range(m)); X = [None] * m
    for i in range(n):
        g = next((g for g in rk[i] if g in free), None)
        if g is not None: X[g] = i; free.discard(g)
    for g in free: X[g] = n - 1
    return X

def w_sd2(a):
    seed, K = a
    rng = random.Random(seed); diff = 0
    for _ in range(K):
        n, m, v = rand_inst(rng, maxk=2)
        if k3s(n, m, v) != sd2(n, m, v): diff += 1
    return diff

if __name__ == '__main__':
    mode = sys.argv[1]
    with multiprocessing.Pool(4) as pool:
        if mode == 'cores':
            N = int(sys.argv[2]); tot = collections.Counter(); bad = []; br = collections.Counter()
            for n, b, x in pool.imap_unordered(w_core, core_profiles(N), chunksize=500):
                tot[n] += 1; bad += b; br[x] += 1
            print(f"cores n <= {N}: {dict(tot)} profiles x {len(REAL)} realizations; not EFX0: {len(bad)}; branches {dict(br)}", bad[:3])
        elif mode == 'coresample':
            # coresample SAMPLE MINN MAXN FILE...: SAMPLE random profiles per core of the given certificate files
            S, lo, hi = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]); files = sys.argv[5:]
            tot = collections.Counter(); bad = []; br = collections.Counter()
            gens = [core_profiles(hi, certs=f, disc=f, sample=S, minn=lo) for f in files]
            src = (x for g in gens for x in g)
            for n, b, x in pool.imap_unordered(w_core, src, chunksize=500):
                tot[n] += 1; bad += b; br[x] += 1
            print(f"core sample ({S} random profiles per core; {' '.join(files)}): {dict(tot)} profiles x {len(REAL)} realizations; not EFX0: {len(bad)}; branches {dict(br)}", bad[:3])
        elif mode == 'small':
            n, m = int(sys.argv[2]), int(sys.argv[3]); tot = 0; bad = []; br = collections.Counter()
            for _, b, x in pool.imap_unordered(w_small, gen_small(n, m), chunksize=2000):
                tot += 1; bad += b; br[x] += 1
            print(f"small n={n} m={m}: {tot} profiles; not EFX0: {len(bad)}; branches {dict(br)}", bad[:3])
        elif mode == 'random':
            K, seed = int(sys.argv[2]), int(sys.argv[3]); bad = []; br = collections.Counter()
            for b, x in pool.imap_unordered(w_rand, [(seed * 1000 + t, K // 100) for t in range(100)]):
                bad += b; br.update(x)
            print(f"random general instances: {K} (seed {seed}); not EFX0: {len(bad)}; branches {dict(br)}", bad[:3])
        elif mode == 'rprof':
            K, seed = int(sys.argv[2]), int(sys.argv[3]); bad = []; br = collections.Counter()
            for b, x in pool.imap_unordered(w_rprof, [(seed * 1000 + t, K // 100) for t in range(100)]):
                bad += b; br.update(x)
            print(f"random ranking profiles (3 goods each, n 2-9, m n..2n+3, worthless goods allowed): {K} (seed {seed}); not EFX0: {len(bad)}; branches {dict(br)}", bad[:3])
        elif mode == 'sd2':
            K, seed = int(sys.argv[2]), int(sys.argv[3])
            d = sum(pool.map(w_sd2, [(seed * 1000 + t, K // 100) for t in range(100)]))
            print(f"<= 2 goods per agent: {K} random instances (seed {seed}); K3S differs from serial dictatorship on {d}")
