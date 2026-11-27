"""Least charity by SAT (kgen/charity.md §1): for random instances in which every agent values KMIN..K goods, the least
number of unallocated goods over partial EFX0 allocations with strong charity (chlib.sat_min_charity).  A value > 0
would refute TARGET_K (and the additive EFX conjecture, by L1).  Witnesses are re-checked with the raw definitions.

    python3 kgen/charity/ch_least.py SEED T NMIN NMAX KMIN K [gen]
gen: 'rand' (m in [n, 2.5n], values 1..100), 'small' (values 1..6, ties frequent), 'hot' (a few goods valued by many)."""
import sys, os, random, collections, time, json, multiprocessing as mp
from chlib import rand_inst, rand_hot, sat_min_charity, efx0, pool_ok


def job(args):
    seed, n, kmin, K, gen = args
    rng = random.Random(seed)
    m = rng.randint(max(n, K), max(n, K, int(2.5 * n)))
    if gen == 'hot':
        I = rand_hot(rng, n, m, K, hot=rng.randint(1, 3))
    else:
        I = rand_inst(rng, n, m, kmin, K, vmax=6 if gen == 'small' else 100)
    t0 = time.time()
    b, X = sat_min_charity(I, strong=True)
    assert X is not None and efx0(I, X) and pool_ok(I, X, strong=True)
    return n, I.k(), b, time.time() - t0, I


if __name__ == '__main__':
    seed, T, NMIN, NMAX, KMIN, K = map(int, sys.argv[1:7]); gen = sys.argv[7] if len(sys.argv) > 7 else 'rand'
    print('$ python3 kgen/charity/ch_least.py', *sys.argv[1:], flush=True)
    C = collections.Counter(); t0 = time.time(); tmax = 0
    tasks = [(seed * 999983 + t, NMIN + t % (NMAX - NMIN + 1), KMIN, K, gen) for t in range(T)]
    with mp.Pool(os.cpu_count()) as pool:
        for n, k, b, dt, I in pool.imap_unordered(job, tasks):
            C['n=%d k=%d least charity %d' % (n, k, b)] += 1; tmax = max(tmax, dt)
            if b:
                print('POSITIVE LEAST CHARITY', json.dumps(I.to_json()), b, flush=True)
    for key in sorted(C):
        print(key, C[key])
    print('slowest instance %.1f s; time %.0f s' % (tmax, time.time() - t0))
