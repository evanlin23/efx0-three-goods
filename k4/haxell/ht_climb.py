"""Adversarial search for counterexamples to CONN_2 and CONN_1 (k4/haxell.md §4).

  CONN_1: every partial EFX0 allocation reaches a complete one in G* (single local moves; ht_gstar.py);
  CONN_2: the same with composite moves of two local moves (no radius-2 trap).
The data say CONN_2 holds everywhere tested and CONN_1 holds at k = 3 and fails at k = 4.  This script samples random
instances (mode 'sample') or hill-climbs from random ones (mode 'climb'), maximizing (radius-2 traps, traps, states
with a trap among the fewest-pool states), and prints every instance with a radius-2 trap, and every instance with a
single-move trap when every agent values at most three goods.

    python3 k4/haxell/ht_climb.py MODE N SEED n m k [VMAX=40] [STEPS=200]
MODE: sample (N random instances) | climb (N climbs of STEPS mutations each)."""
import sys, os, json, random, itertools, collections, time
import multiprocessing as mpc
from ht_lib import Inst
from ht_gstar import traps, radius2_traps


def rand_inst(rng, n, m, k, vmax):
    while True:
        sets = [sorted(rng.sample(range(m), min(k, m))) for _ in range(n)]
        if len(set().union(*map(set, sets))) == m:
            break
    vals = [[rng.randint(1, vmax) for _ in s] for s in sets]
    return sets, vals


def score(sets, vals, m):
    I = Inst(sets, vals, m)
    S, comp, T = traps(I)
    T2 = radius2_traps(I, S, T) if T else set()
    return (len(T2), len(T), -len(comp)), len(comp), T, T2


def mutate(rng, sets, vals, m, k, vmax):
    sets = [list(s) for s in sets]; vals = [list(v) for v in vals]
    i = rng.randrange(len(sets))
    if rng.random() < 0.8:
        j = rng.randrange(len(sets[i])); vals[i][j] = rng.randint(1, vmax)
    else:
        j = rng.randrange(len(sets[i]))
        out = [g for g in range(m) if g not in sets[i]]
        if out:
            g = rng.choice(out); sets[i][j] = g
            order = sorted(range(len(sets[i])), key=lambda t: sets[i][t])
            sets[i] = [sets[i][t] for t in order]; vals[i] = [vals[i][t] for t in order]
    if len(set().union(*map(set, sets))) < m:
        return None
    return sets, vals


def report(tag, sets, vals, m, comp, nT, nT2, ex, k):
    if nT2:
        print('RADIUS-2 TRAP', tag, json.dumps((sets, vals)), 'm', m, 'complete', comp, 'traps', nT, 'r2', nT2,
              'e.g.', ex, flush=True)
    if nT and max(len(s) for s in sets) <= 3:
        print('k<=3 TRAP', tag, json.dumps((sets, vals)), 'm', m, 'traps', nT, flush=True)


def job(args):
    mode, seed, n, m, k, vmax, steps = args
    rng = random.Random(seed); C = collections.Counter(); out = []
    if mode == 'sample':
        sets, vals = rand_inst(rng, n, m, k, vmax)
        sc, comp, T, T2 = score(sets, vals, m)
        return [(sc, sets, vals, comp, len(T), len(T2), [list(t) for t in list(T2)[:1]])]
    sets, vals = rand_inst(rng, n, m, k, vmax)
    sc, comp, T, T2 = score(sets, vals, m); best = (sc, sets, vals, comp, len(T), len(T2), [])
    for _ in range(steps):
        r = mutate(rng, sets, vals, m, k, vmax)
        if r is None:
            continue
        s2, v2 = r
        sc2, comp2, T2_, T22 = score(s2, v2, m)
        if comp2 == 0:
            print('NO COMPLETE EFX0 ALLOCATION', json.dumps((s2, v2)), m, flush=True)
        if sc2 >= sc:
            sets, vals, sc = s2, v2, sc2
            if sc2 > best[0]:
                best = (sc2, s2, v2, comp2, len(T2_), len(T22), [list(t) for t in list(T22)[:1]])
    return [best]


if __name__ == '__main__':
    mode = sys.argv[1]; N, seed, n, m, k = map(int, sys.argv[2:7])
    args = dict(a.split('=') for a in sys.argv[7:] if '=' in a)
    vmax = int(args.get('VMAX', '40')); steps = int(args.get('STEPS', '200'))
    print('$ python3 k4/haxell/ht_climb.py', *sys.argv[1:], flush=True)
    t0 = time.time(); C = collections.Counter(); top = []
    tasks = [(mode, seed * 1000003 + t, n, m, k, vmax, steps) for t in range(N)]
    with mpc.Pool(os.cpu_count()) as pool:
        for res in pool.imap_unordered(job, tasks, chunksize=8 if mode == 'sample' else 1):
            for sc, sets, vals, comp, nT, nT2, ex in res:
                C['runs'] += 1; C['with a trap'] += nT > 0; C['with a radius-2 trap'] += nT2 > 0
                report(mode, sets, vals, m, comp, nT, nT2, ex, k)
                top.append((sc, sets, vals))
    top.sort(key=lambda x: x[0], reverse=True)
    for sc, sets, vals in top[:3]:
        print('BEST score (radius-2 traps, traps, -complete) =', sc, json.dumps((sets, vals)), flush=True)
    for key in sorted(C):
        print(key, C[key])
    print('time %.0f s' % (time.time() - t0))
