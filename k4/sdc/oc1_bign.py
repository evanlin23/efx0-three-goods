"""OC1 (k4/sdc.md §29) beyond n = 5.  Every earlier test of OC1 stopped at n <= 5 (every order).  Here: random k = 4
instances with n = 6..9 (generator 'big<n>' of sdc_rand.py: degrees 3/4, m in [n+4, 2.5n]), a sample of orders per
instance (always including the identity and its reverse), and for each start: do the picks have a one-absorber EFX0
completion (oc_absorb.extends_A, A = 1)?  If not, does one improving chain (de_free.iter_chains, generated lazily,
stopping at the first repairing one) give a state that has one?  A start with neither is a counterexample to OC1.
A per-start time limit marks a start 'timeout' instead (reported separately, never counted as a pass).

    python3 k4/sdc/oc1_bign.py N_INST ORDERS SEED NMIN NMAX [TLIM]"""
import sys, os, json, random, itertools, collections, time, multiprocessing as mp
import _paths
import de_free as DF
from oc_absorb import extends_A
from sdclib import Enc
from sdc_orders import sd

DF.CHAIN_ONLY = True


def gen(n, rng):
    cwd = os.getcwd(); os.chdir(_paths.DE4)
    from de4lib import random_profile
    os.chdir(cwd)
    m = rng.randint(n + 4, 2 * n + n // 2)
    while True:
        sets = [sorted(rng.sample(range(m), rng.choice([3, 4, 4]))) for _ in range(n)]
        if len(set().union(*map(set, sets))) == m: break
    return sets, random_profile(sets, rng), m


def check_start(E, Y, tlim):
    base = [-1] * E.m
    for i, g in enumerate(Y):
        if g is not None: base[g] = i
    base = tuple(base)
    if extends_A(E, base, 1): return 0, None
    t0 = time.time(); seen = set()
    for b2 in DF.iter_chains(E, base):
        if b2 in seen: continue
        seen.add(b2)
        if extends_A(E, b2, 1): return 1, b2
        if time.time() - t0 > tlim: return 'timeout', None
    return None, None


def job(args):
    n, orders, seed, tlim = args
    rng = random.Random(seed)
    sets, vals, m = gen(n, rng)
    E = Enc(sets, vals, m)
    out = collections.Counter(); bad = []
    ords = [list(range(n)), list(range(n))[::-1]]
    while len(ords) < orders:
        o = list(range(n)); rng.shuffle(o); ords.append(o)
    done = {}
    for o in ords:
        Y = tuple(sd(E, o)[0])
        if Y not in done: done[Y] = check_start(E, Y, tlim)[0]
        r = done[Y]; out['starts: chains needed %s' % r] += 1
        if r is None: bad.append((o, Y))
    return n, seed, sets, vals, m, out, bad


if __name__ == '__main__':
    N, ORD, SEED, NMIN, NMAX = map(int, sys.argv[1:6])
    TLIM = float(sys.argv[6]) if len(sys.argv) > 6 else 120.0
    print('$ python3 k4/sdc/oc1_bign.py', *sys.argv[1:], flush=True)
    t0 = time.time(); C = collections.Counter()
    tasks = [(NMIN + (t % (NMAX - NMIN + 1)), ORD, SEED * 100003 + t, TLIM) for t in range(N)]
    with mp.Pool(max(1, os.cpu_count())) as pool:
        for n, seed, sets, vals, m, out, bad in pool.imap_unordered(job, tasks):
            C['instances n=%d' % n] += 1
            for k, v in out.items(): C['n=%d %s' % (n, k)] += v
            if bad:
                C['instances with an unrepaired start'] += 1
                print('OC1 FAILS', json.dumps({'n': n, 'm': m, 'seed': seed, 'sets': sets, 'vals': vals,
                                               'order': bad[0][0], 'picks': bad[0][1]}), flush=True)
            if any('timeout' in k for k in out): print('timeout on seed', seed, 'n', n, dict(out), flush=True)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
