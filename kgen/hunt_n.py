"""OC1 and its variants with n agents (n <= 5), any k: random hunt with the brute force kgen/ocn.c, and (xcheck mode)
a cross-check of ocn.c's OC1 status (t >= 0) against k4/sdc's SAT pipeline (oc_absorb.extends_A + de_free.iter_chains,
sets unbounded).

    python3 kgen/hunt_n.py hunt N_AGENTS SEED COUNT MMIN MMAX
    python3 kgen/hunt_n.py xcheck N_AGENTS SEED COUNT MMIN MMAX
kinds (cycled): klim:3, klim:4, klim:6, general, zeros, ident, junk."""
import sys, os, random, json, time, collections, itertools, multiprocessing as mp
from ocnlib import brute_n

HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE)
KINDS = ['klim:3', 'klim:4', 'klim:6', 'general', 'zeros', 'ident', 'junk']


def gen_n(kind, n, m, rng):
    while True:
        v = [[0] * m for _ in range(n)]
        if kind.startswith('klim'):
            K = int(kind.split(':')[1]); m2 = min(m, n * K)
            v = [[0] * m2 for _ in range(n)]; m_ = m2
            size = [rng.randint(2, min(K, m_)) for _ in range(n)]
            if sum(size) < m_: continue
            S = [set() for _ in range(n)]
            for g in rng.sample(range(m_), m_):
                i = rng.choice([a for a in range(n) if len(S[a]) < size[a]]); S[i].add(g)
            for i in range(n):
                while len(S[i]) < size[i]: S[i].add(rng.randrange(m_))
                for g, x in zip(sorted(S[i]), rng.sample(range(1, 100), len(S[i]))): v[i][g] = x
        elif kind == 'general':
            v = [rng.sample(range(1, 100), m) for _ in range(n)]
        elif kind == 'zeros':
            for i in range(n):
                S = [g for g in range(m) if rng.random() > 1 / 3]
                for g, x in zip(S, rng.sample(range(1, 100), len(S))): v[i][g] = x
        elif kind == 'ident':
            base = [rng.randint(5, 60) for _ in range(m)]
            for i in range(n):
                while True:
                    row = [max(1, b * 4 + rng.randint(-6, 6)) for b in base]
                    if len(set(row)) == m: break
                v[i] = row
        elif kind == 'junk':
            for i in range(n):
                big = rng.sample(range(m), rng.randint(1, 2)); xs = rng.sample(range(1, 41), m)
                v[i] = [x if g not in big else x + rng.randint(20, 80) for g, x in enumerate(xs)]
                for g in range(m):
                    if g not in big and rng.random() < 0.3: v[i][g] = 0
                pos = [x for x in v[i] if x > 0]
                if len(set(pos)) < len(pos): v[i] = [0] * m
        mm = len(v[0])
        if all(any(v[i][g] > 0 for i in range(n)) for g in range(mm)) and all(any(r) for r in v):
            return v


def sat_status(v):
    sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
    import _paths  # noqa
    import de_free as DF
    from sdclib import Enc
    from oc_absorb import extends_A
    from sdc_orders import sd
    n, m = len(v), len(v[0]); DF.CHAIN_ONLY = True; DF.HMAX = m; DF.BMAX = m
    sets = [[g for g in range(m) if v[i][g] > 0] for i in range(n)]
    E = Enc(sets, [[v[i][g] for g in sets[i]] for i in range(n)], m); res = []; memo = {}
    for o in itertools.permutations(range(n)):
        Y = tuple(sd(E, list(o))[0])
        if Y not in memo:
            base = [-1] * m
            for i, g in enumerate(Y):
                if g is not None: base[g] = i
            base = tuple(base)
            if extends_A(E, base, 1): memo[Y] = 0
            elif any(extends_A(E, b2, 1) for b2 in set(DF.iter_chains(E, base))): memo[Y] = 1
            else: memo[Y] = None
        res.append(memo[Y])
    return res


def job(args):
    mode, n, seed, kind, m = args
    rng = random.Random(seed); v = gen_n(kind, n, m, rng)
    orders, r = brute_n(v)
    st = [0 if d['NONE'] else (1 if d['CODE'] else None) for d in r]
    sat = sat_status(v) if mode == 'xcheck' else None
    return kind, v, orders, r, st, sat


if __name__ == '__main__':
    mode = sys.argv[1]; n, seed, N, lo, hi = map(int, sys.argv[2:7])
    print('$ python3 kgen/hunt_n.py', *sys.argv[1:], flush=True); t0 = time.time()
    rng = random.Random(seed); C = collections.Counter()
    tasks = [(mode, n, seed * 1000003 + t, KINDS[t % len(KINDS)], rng.randint(lo, hi)) for t in range(N)]
    with mp.Pool(os.cpu_count()) as pool:
        for kind, v, orders, r, st, sat in pool.imap_unordered(job, tasks):
            C['instances %s' % kind] += 1
            if r[0]['EFX'] == 0: C['NO EFX0'] += 1; print('NO EFX0', json.dumps(v), flush=True); continue
            for o, d in enumerate(r):
                C['starts'] += 1; C['starts: chains needed %s' % st[o]] += 1
                for key in ['CODE', 'STRICT', 'FREEOC', 'MD']:
                    if d[key] == 0:
                        C['FAIL %s' % key] += 1
                        if C['shown %s' % key] < 4:
                            C['shown %s' % key] += 1
                            print('FAIL', key, kind, json.dumps(v), 'order', orders[o], 'picks', d['picks'], flush=True)
            if not any(d['FREE0'] for d in r): C['FAIL SD-C'] += 1; print('FAIL SD-C', json.dumps(v), flush=True)
            if sat is not None and sat != st:
                C['MISMATCH'] += 1; print('MISMATCH', json.dumps(v), 'brute', st, 'sat', sat, flush=True)
    for k in sorted(C):
        if not k.startswith('shown'): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
