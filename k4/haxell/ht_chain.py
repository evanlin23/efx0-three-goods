"""The chain lemma (k4/haxell.md §6, "Alternating chains"): from every partial EFX0 allocation with a nonempty pool, an
alternating chain of moves reaches a partial EFX0 allocation with a smaller pool, or with the same pool and a Pareto
improvement (no agent worse, some agent strictly better).

A chain (as in ht_rescue.py) starts at the pool: move 1 gives a nonempty set of pooled goods to an agent a1, or swaps a
pooled good with one of a1's goods.  Move t >= 2 gives a nonempty set of a_{t-1}'s goods to an agent a_t != a_{t-1}, or
swaps one of a_{t-1}'s goods with one of a_t's.  Intermediate states are arbitrary (they need not be EFX0); agents may
recur.  The search is a breadth-first search over (state, current agent), so it finds a shortest chain.

Pure Python from the raw definition (ht_rescue.py's Inst; no code shared with gstar_measure.c).  For every partial
EFX0 state with a nonempty pool of every instance: the length of a shortest improving chain, up to L.

    python3 k4/haxell/ht_chain.py GEN=n2 [K=4] [L=6]            every strict type profile at n = 2 (ht_n2types.py)
    python3 k4/haxell/ht_chain.py GEN=n3 [K=3] [MMAX=9] [L=6]   every strict type profile at n = 3 (ht_n3types.py)
    python3 k4/haxell/ht_chain.py GEN=cores [N=5] [MMIN=4] [MMAX=7] [SEED=1] [DOMAIN=cert] [L=6]
                                  N random type profiles of every n = 4, k = 4 core (ht_n4core.py's sampler)
    python3 k4/haxell/ht_chain.py GEN=stdin [L=6] < lines       instance lines "n m d g v ... d g v ..."
    [LIMIT=0] [PROCS=1] [AUG=0]
AUG=1 also finds, at every state, a shortest *augmenting* chain (its first move gives pooled goods to an agent, so the
pool shrinks: no measure involved), and counts the states that have none within L."""
import sys, os, itertools, collections, time
import multiprocessing as mpc
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
ARGV = sys.argv[1:]; KW = dict(a.split('=') for a in ARGV if '=' in a)
GEN = KW.get('GEN', 'stdin'); L = int(KW.get('L', '6')); LIMIT = int(KW.get('LIMIT', '0'))
PROCS = int(KW.get('PROCS', '1')); AUG = int(KW.get('AUG', '0'))
import ht_rescue as R


def lines():
    if GEN == 'n2':
        sys.argv = ['x', 'K=' + KW.get('K', '4')]
        import ht_n2types as T
        for m, vA, vB in T.instances():
            yield T.line(m, vA, vB)
    elif GEN == 'n3':
        sys.argv = ['x', 'K=' + KW.get('K', '3'), 'MMAX=' + KW.get('MMAX', '9')]
        import ht_n3types as T
        for m, key in T.G.shapes():
            yield from T.instances(m, key)
    elif GEN == 'cores':
        sys.argv = ['x', 'DOMAIN=' + KW.get('DOMAIN', 'cert')]
        import ht_n4core as C, random
        rng = random.Random(int(KW.get('SEED', '1'))); N = int(KW.get('N', '5'))
        for fname, c in C.load_cores():
            sets, m = c['sets'], c['m']
            if not (int(KW.get('MMIN', '4')) <= m <= int(KW.get('MMAX', '7'))):
                continue
            deg = [sum(g in S for S in sets) for g in range(m)]
            doms = [C.domain(S, deg) for S in sets]
            for _ in range(N):
                yield C.line(sets, m, [rng.choice(d) for d in doms])
    else:
        for ln in sys.stdin:
            if ln.strip():
                yield ln.strip()


def run(ln):
    n, m, val, rel = R.parse_inst(ln.split()); I = R.Inst(n, m, val); h = collections.Counter(); bad = []; worst = None
    ha = collections.Counter(); abad = []
    for o in itertools.product(list(range(n)) + [R.POOL], repeat=m):
        if R.POOL in o and I.efx0(o):
            path = R.shortest_chain(n, m, val, o, L, I=I)
            k = len(path) if path else None; h[k] += 1
            if AUG:
                apath = path if path and path[0][0] == 'T' else R.shortest_chain(n, m, val, o, L, aug=True, I=I)
                ha[len(apath) if apath else None] += 1
                if apath is None:
                    abad.append(o)
            if path is None:
                bad.append(o)
            elif worst is None or k > worst[0]:
                worst = (k, o, R.pattern(path))
    return ln, h, bad, worst, ha, abad


if __name__ == '__main__':
    print('$ python3 k4/haxell/ht_chain.py', *ARGV, flush=True)
    t0 = time.time(); tot = collections.Counter(); ninst = 0; nbad = 0; longest = None
    atot = collections.Counter(); nabad = 0
    src = lines()
    if LIMIT:
        src = itertools.islice(src, LIMIT)
    with mpc.Pool(PROCS) as pool:
        for ln, h, bad, worst, ha, abad in pool.imap_unordered(run, src, chunksize=16):
            ninst += 1
            for k, c in ha.items():
                atot[k] += c
            if abad:
                nabad += 1
                if nabad <= 10:
                    print('NO AUGMENTING CHAIN within %d at %d states, e.g. %s | %s' % (L, len(abad), abad[0], ln), flush=True)
            for k, c in h.items():
                tot[k] += c
            if bad:
                nbad += 1
                if nbad <= 20:
                    print('NO CHAIN within %d at %d states, e.g. %s | %s' % (L, len(bad), bad[0], ln), flush=True)
            if worst and (longest is None or worst[0] > longest[0]):
                longest = worst + (ln,)
                print('longest so far: %d at state %s (%s) | %s' % longest, flush=True)
            if ninst % 5000 == 0:
                print('... %d instances, %.0f s' % (ninst, time.time() - t0), flush=True)
    print('instances', ninst, 'partial EFX0 states with a nonempty pool', sum(tot.values()))
    print('shortest improving chain length: states', dict(sorted(tot.items(), key=lambda x: (x[0] is None, x[0] or 0))))
    print('instances with a state that has no chain within %d: %d' % (L, nbad))
    if AUG:
        print('shortest augmenting chain length: states', dict(sorted(atot.items(), key=lambda x: (x[0] is None, x[0] or 0))))
        print('instances with a state that has no augmenting chain within %d: %d' % (L, nabad))
    print('time %.0f s' % (time.time() - t0))
