"""Conjecture W at sampled states of instances too large for the census (k4/haxell.md §7): random instances with
n agents, m goods, k relevant goods each (values 1..40, or 1..VMAX with ties); for each, START states (the empty
allocation, the serial-dictatorship picks of a random order, and states reached from them by random EFX0-preserving
walks of up to LEN single moves, swaps and trades, the pool never growing); at each state the exact augmenting search
and the partial welfare search of ht_wlocal.Loc.check, then a W-walk to a complete allocation.  A state where no step
is found is reported: it refutes W if the augmenting part (exhaustive) and a full welfare search (not implemented for
rotation plus move) both fail, so such a state is printed for a separate exhaustive check.

    python3 k4/haxell/ht_wsample.py N SEED n m k [START=6] [LEN=30] [VMAX=40]"""
import sys, os, random, json, collections, time
import multiprocessing as mpc
from ht_wlocal import Loc, walk, apply_step
from ht_lib import Inst, sd


def rand_inst(rng, n, m, k, vmax):
    while True:
        sets = [sorted(rng.sample(range(m), min(k, m))) for _ in range(n)]
        if len(set().union(*map(set, sets))) == m:
            break
    vals = [[rng.randint(1, vmax) for _ in s] for s in sets]
    return sets, vals


def random_walk(L, own, rng, ln):
    own = tuple(own)
    for _ in range(ln):
        cand = list(L.simple(own))
        for a in range(L.n):
            for b in range(a + 1, L.n):
                cand.append((tuple(b if x == a else a if x == b else x for x in own), ('trade', a, b)))
        rng.shuffle(cand)
        for t, mv in cand[:200]:
            if t.count(-1) <= own.count(-1) and L.efx0(t):
                own = t; break
    return own


def job(args):
    t, seed, n, m, k, nstart, ln, vmax = args
    rng = random.Random(seed)
    sets, vals = rand_inst(rng, n, m, k, vmax)
    L = Loc(sets, vals, m)
    C = collections.Counter(); bad = []
    starts = [tuple([-1] * m)]
    o = list(range(n)); rng.shuffle(o)
    Y = sd(Inst(sets, vals, m), o)[0]
    pk = [-1] * m
    for i, g in enumerate(Y):
        if g is not None:
            pk[g] = i
    starts.append(tuple(pk))
    while len(starts) < nstart:
        starts.append(random_walk(L, rng.choice(starts[:2]), rng, rng.randint(1, ln)))
    for st in starts:
        if -1 not in st:
            C['complete start'] += 1; continue
        kind, how = L.check(st)
        C['step %s' % kind] += 1
        if kind is None:
            bad.append(st); continue
        ok, steps = walk(L, st)
        C['walk %s' % ('complete' if ok else 'stuck' if ok is False else 'cap')] += 1
        if ok is False:
            bad.append(st)
    return sets, vals, C, bad


if __name__ == '__main__':
    N, SEED, n, m, k = map(int, sys.argv[1:6])
    args = dict(a.split('=') for a in sys.argv[6:] if '=' in a)
    nstart = int(args.get('START', '6')); ln = int(args.get('LEN', '30')); vmax = int(args.get('VMAX', '40'))
    print('$ python3 k4/haxell/ht_wsample.py', *sys.argv[1:], flush=True)
    t0 = time.time(); C = collections.Counter()
    tasks = [(t, SEED * 1000003 + t, n, m, k, nstart, ln, vmax) for t in range(N)]
    with mpc.Pool(os.cpu_count()) as pool:
        for sets, vals, c, bad in pool.imap_unordered(job, tasks):
            C['instances'] += 1
            for key, v in c.items():
                C[key] += v
            for st in bad[:2]:
                print('NO STEP FOUND', json.dumps((sets, vals)), 'state', list(st), flush=True)
    for key in sorted(C):
        print(key, C[key])
    print('time %.0f s' % (time.time() - t0))
