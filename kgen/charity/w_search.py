"""Question W (kgen/charity.md §6): is the welfare maximum over partial EFX0 allocations, among those with the fewest
unallocated goods, complete?  For each instance: chlib.welfare_max (SAT with a reachable-partial-sums encoding of
'total >= W', binary search, then the fewest unallocated goods at that total).  Prints every instance whose welfare
maximum strands a good.

    python3 kgen/charity/w_search.py SOURCE SEED T [NMIN NMAX KMIN K VMAX]
SOURCE: 'screen' (168 curated k = 4 instances), 'rand' (random, agents value KMIN..K goods, values 1..VMAX),
        'family' (S(sigma, 3) and S'(sigma, 3), sigma = 2..5)."""
import sys, os, json, random, collections, time, multiprocessing as mp
from chlib import Inst, from_sets, rand_inst, welfare_max, pool_of, efx0


def job(args):
    tag, I = args
    t0 = time.time()
    W, p, X = welfare_max(I)
    return tag, I, W, p, X, time.time() - t0


if __name__ == '__main__':
    src, SEED, T = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    print('$ python3 kgen/charity/w_search.py', *sys.argv[1:], flush=True)
    tasks = []
    if src == 'screen':
        from ch_screen import load
        tasks = [(name, from_sets(sets, vals, m)) for name, sets, vals, m in load()]
    elif src == 'family':
        from stuck_family import build
        tasks = [('%s(%d,3)' % ("S'" if own else 'S', s), build(s, 3, own=own)[0])
                 for s in range(2, 6) for own in (False, True)]
    else:
        NMIN, NMAX, KMIN, K, VMAX = map(int, sys.argv[4:9]); rng = random.Random(SEED)
        for t in range(T):
            n = rng.randint(NMIN, NMAX); m = rng.randint(max(n, K), max(n, K, 2 * n + 2))
            tasks.append(('rand#%d' % t, rand_inst(rng, n, m, KMIN, K, vmax=VMAX, cover=False)))
    C = collections.Counter(); t0 = time.time(); tmax = 0
    with mp.Pool(os.cpu_count()) as pool:
        for tag, I, W, p, X, dt in pool.imap_unordered(job, tasks):
            C['instances'] += 1; C['welfare maximum leaves %d out' % p] += 1; tmax = max(tmax, dt)
            if p:
                print('STRANDED', tag, I.n, I.m, I.k(), 'welfare', W, json.dumps({'inst': I.to_json(),
                      'X': [sorted(B) for B in X], 'pool': sorted(pool_of(I, X))}), flush=True)
    for key in sorted(C):
        print(key, C[key])
    print('slowest %.1f s; time %.0f s' % (tmax, time.time() - t0))
