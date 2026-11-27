"""How many goods can a Pareto maximum leave out?  (kgen/charity.md, Question PM.)

A *Pareto maximum* is a partial EFX0 allocation that no partial EFX0 allocation Pareto-dominates, and that allocates
the most goods among those with its value vector (the hypothesis of K4.SDC.P1).  Every Pareto maximum is a robust CKMS
stopping state with strong charity (Lemma CH6), so Lemmas CH1-CH5 apply to it.  For each instance this script asks,
exactly (chlib.pm_with_pool, CEGAR over Pareto maxima), whether some Pareto maximum leaves at least MINPOOL goods out.

    python3 kgen/charity/pm_search.py SOURCE MINPOOL SEED T [NMIN NMAX K]
SOURCE: 'screen' (the 168 k = 4 screen instances), 'rand' (random, agents value 2..K goods, values 1..12),
        'core' (random, agents value K-1..K goods, values 1..12), 'family' (stuck_family.build(sigma, 3), sigma 2..4)."""
import sys, os, json, random, collections, time, multiprocessing as mp
from chlib import Inst, from_sets, rand_inst, pm_with_pool, pool_of, efx0


def job(args):
    tag, I, minpool, tlim = args
    t0 = time.time()
    X, st = pm_with_pool(I, minpool)
    return tag, I.n, I.m, I.k(), X, st, time.time() - t0, I


if __name__ == '__main__':
    src, MINPOOL, SEED, T = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    print('$ python3 kgen/charity/pm_search.py', *sys.argv[1:], flush=True)
    tasks = []
    if src == 'screen':
        from ch_screen import load
        for name, sets, vals, m in load():
            tasks.append((name, from_sets(sets, vals, m), MINPOOL, None))
    elif src == 'family':
        from stuck_family import build
        for sigma in range(2, 5):
            tasks.append(('family sigma=%d' % sigma, build(sigma, 3)[0], MINPOOL, None))
    else:
        NMIN, NMAX, K = map(int, sys.argv[5:8]); rng = random.Random(SEED)
        for t in range(T):
            n = rng.randint(NMIN, NMAX); m = rng.randint(n + 1, min(2 * n + 2, n * K))
            kmin = 2 if src == 'rand' else K - 1
            tasks.append(('%s#%d' % (src, t), rand_inst(rng, n, m, kmin, K, vmax=12), MINPOOL, None))
    C = collections.Counter(); t0 = time.time()
    with mp.Pool(os.cpu_count()) as pool:
        for tag, n, m, k, X, st, dt, I in pool.imap_unordered(job, tasks):
            C['instances'] += 1; C['Pareto maxima enumerated'] += st['maxima']
            if X is not None:
                C['instances with a Pareto maximum leaving >= %d out' % MINPOOL] += 1
                assert efx0(I, X)
                print('FOUND', tag, n, m, k, json.dumps({'inst': I.to_json(), 'X': [sorted(B) for B in X],
                                                          'pool': sorted(pool_of(I, X))}), flush=True)
    for key in sorted(C):
        print(key, C[key])
    print('time %.0f s' % (time.time() - t0))
