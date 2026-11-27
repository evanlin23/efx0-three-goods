"""Where CKMS's update rules stop on k-relevant instances (kgen/charity.md §2).

For random instances in which every agent values 2..k goods, run CKMS (chlib.ckms: U0, U1, U2 along a shortest
rainbow cycle, envy-cycle elimination) from the empty allocation and from serial-dictatorship picks, with random
tie-breaks, and record the number of unallocated goods at the stopping state.  Every stopping state is checked
against the raw definitions (EFX0, strong charity) and against Lemmas CH1-CH4 (chlib.stuck_report).  When the
pool is nonempty, the least charity (SAT, chlib.sat_min_charity) is computed too, so a nonzero stop that the
instance does not force is told apart from a forced one (a forced one would refute TARGET_k).

    python3 kgen/charity/ch_ckms.py SEED T NMIN NMAX K RUNS [gen]
gen: 'rand' (default; m in [n, 2.5n], degrees 2..K) or 'hot' (a few goods valued by many agents)."""
import sys, os, json, random, collections, time, multiprocessing as mp
from chlib import rand_inst, rand_hot, ckms, stuck_report, efx0, pool_ok, sat_min_charity, Inst


def sd_start(I, rng):
    order = list(range(I.n)); rng.shuffle(order)
    X = [set() for _ in range(I.n)]; free = set(range(I.m))
    for i in order:
        best = max((g for g in free if g in I.R[i]), key=lambda g: (I.v[i][g], -g), default=None)
        if best is not None:
            X[i].add(best); free.discard(best)
    return X


def job(args):
    seed, n, K, runs, gen = args
    rng = random.Random(seed)
    m = rng.randint(n, max(n, int(2.5 * n)))
    I = rand_hot(rng, n, m, K, hot=rng.randint(1, 3)) if gen == 'hot' else rand_inst(rng, n, m, 2, K)
    out = collections.Counter(); wit = None
    for r in range(runs):
        start = 'empty' if r % 2 == 0 else 'sd'
        X0 = None if start == 'empty' else sd_start(I, rng)
        X, P, c, tab = ckms(I, X=X0, rng=rng)
        assert efx0(I, X) and pool_ok(I, X, P, strong=True)
        rep = stuck_report(I, X, P, tab)
        out['%s: pool %d' % (start, len(P))] += 1
        if P:                                   # continue with every champion option (robust stop)
            X, P, c, tab = ckms(I, X=X, rng=rng, mode='all')
            assert efx0(I, X) and pool_ok(I, X, P, strong=True)
            rep = stuck_report(I, X, P, tab)
            out['%s: robust pool %d' % (start, len(P))] += 1
        if P and wit is None:
            wit = {'inst': I.to_json(), 'X': [sorted(B) for B in X], 'P': sorted(P), 'start': start, 'rep': rep}
    least = None
    if wit is not None:
        least, _ = sat_min_charity(I, strong=True, upto=0)
        least = 0 if least == 0 else '>0'
    return n, K, out, wit, least


if __name__ == '__main__':
    seed, T, NMIN, NMAX, K, RUNS = map(int, sys.argv[1:7])
    gen = sys.argv[7] if len(sys.argv) > 7 else 'rand'
    print('$ python3 kgen/charity/ch_ckms.py', *sys.argv[1:], flush=True)
    t0 = time.time(); C = collections.Counter(); W = []
    tasks = [(seed * 1000003 + t, NMIN + t % (NMAX - NMIN + 1), K, RUNS, gen) for t in range(T)]
    with mp.Pool(os.cpu_count()) as pool:
        for n, K_, out, wit, least in pool.imap_unordered(job, tasks):
            C['instances n=%d' % n] += 1
            for key, val in out.items():
                C['n=%d %s' % (n, key)] += val
            if wit is not None:
                C['instances with a nonzero stop'] += 1
                C['  of which least charity %s' % least] += 1
                if len(W) < 5 or len(wit['P']) >= 2:
                    W.append(wit)
                    print('NONZERO STOP', json.dumps(wit), 'least charity', least, flush=True)
    for key in sorted(C):
        print(key, C[key])
    print('time %.0f s' % (time.time() - t0))
