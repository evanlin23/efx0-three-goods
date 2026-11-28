"""attempts/k4-one-local-gadget.md, part 2: TARGET4 with one 4-good agent z by hiding one of z's goods (making the
instance 3-limited), running K3ALG (k3/k3algo.py `fast`, proved EFX0 on 3-limited instances), and optionally moving the
hidden good to z.  Random instances: k3algo.random_core (every agent 3 balanced goods) plus one extra good for z.
    python3 attempts/k4_one_hide_k3alg.py N"""
import sys, os, random, collections, itertools
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'k3'))
import k3algo as K
from multiprocessing import Pool

def inst(seed):
    rng = random.Random(seed)
    n = rng.randint(2, 6); m = rng.randint(n + 1, 2 * n + 3)
    v = K.random_core(n, m, rng) if hasattr(K, 'random_core') else None
    z = rng.randrange(n)
    cand = [g for g in range(m) if g not in v[z]]
    if len(v[z]) != 3 or not cand: return None
    g = rng.choice(cand); v[z] = dict(v[z]); v[z][g] = rng.randint(1, 100)
    return n, m, v, z

def job(seed):
    r = inst(seed)
    if r is None: return None
    n, m, v, z = r
    vals = sorted(v[z], key=lambda g: v[z][g])
    res = []
    for h in vals:                         # least first
        vh = [dict(d) for d in v]; del vh[z][h]
        X, _ = K.fast(n, m, vh)
        res.append(K.raw_efx0(n, m, v, X))
    return res

def main1(N):
    C = collections.Counter(); bad = []
    with Pool(4) as p:
        for s, r in zip(range(N), p.imap(job, range(N), chunksize=64)):
            if r is None: continue
            C['instances'] += 1
            C['hide least good works: %s' % r[0]] += 1
            C['some hidden good works: %s' % any(r)] += 1
            if not any(r) and len(bad) < 3: bad.append(s)
    for k in sorted(C): print(k, C[k])
    print('seeds where no hidden good works:', bad)

def job2(seed):
    r = inst(seed)
    if r is None: return None
    n, m, v, z = r
    vals = sorted(v[z], key=lambda g: v[z][g])
    out = {'plain': [], 'move': [], 'where': []}
    for h in vals:
        vh = [dict(d) for d in v]; del vh[z][h]
        X, _ = K.fast(n, m, vh)
        ok = K.raw_efx0(n, m, v, X); out['plain'].append(ok)
        holder = X[h]; sizes = collections.Counter(X)
        out['where'].append('z' if holder == z else ('big' if sizes[holder] > 2 else 'small'))
        X2 = list(X); X2[h] = z
        out['move'].append(ok or K.raw_efx0(n, m, v, X2))
    return out

def main2(N):
    C = collections.Counter(); bad = []
    with Pool(4) as p:
        for s, r in zip(range(N), p.imap(job2, range(N), chunksize=64)):
            if r is None: continue
            C['instances'] += 1
            if not r['plain'][0]: C['least hidden fails; hidden good was in: %s' % r['where'][0]] += 1
            C['least hidden, + move it to z: %s' % r['move'][0]] += 1
            C['some hidden good, + move: %s' % any(r['move'])] += 1
            if not any(r['move']) and len(bad) < 3: bad.append(s)
    for k in sorted(C): print(k, C[k])
    print('seeds failing everything:', bad)


if __name__ == '__main__':
    N = int(sys.argv[1])
    print('$ python3 attempts/k4_one_hide_k3alg.py', N, flush=True)
    main2(N)
    v = [{1: 98, 4: 86, 0: 27}, {1: 36, 4: 33, 3: 10, 0: 12}]; n, m = 2, 5
    print('smallest failure (n = 2, m = 5, z = agent 1, good 2 valued by nobody):', v)
    print('  EFX0 allocations:', [[[g for g in range(m) if X[g] == i] for i in range(n)]
                                 for X in itertools.product(range(n), repeat=m) if K.raw_efx0(n, m, v, list(X))])
    for h in sorted(v[1], key=lambda g: v[1][g]):
        vh = [dict(d) for d in v]; del vh[1][h]; X, _ = K.fast(n, m, vh); X2 = list(X); X2[h] = 1
        print('  hide %d: K3ALG gives %s, EFX0 %s; moving %d to z: EFX0 %s' % (
            h, [[g for g in range(m) if X[g] == i] for i in range(n)], K.raw_efx0(n, m, v, X), h, K.raw_efx0(n, m, v, X2)))
