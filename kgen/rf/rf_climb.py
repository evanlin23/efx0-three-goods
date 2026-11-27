"""Adversarial search for a violation of RF (rf_lib.py): hill climbs on the values of a fixed hypergraph, seeded at the
known k >= 5 one-chain failures (rf_known.py's list) and at random strict cores (rf_run.gen_sets).

Score of an instance (larger = closer to an RF violation):
  no failing maximum-matching start:  (0, -fewest completable states over max starts)   -- push toward a failing start
  some failing max start Y:           (1, -fewest completable states over the receiver-first max orders' picks Y')
where 'completable states' of picks Y' counts the states among {Y'} and every state one official move reaches that
have a one-absorber completion; 0 means OC1 fails at Y', i.e. an RF violation.  Values stay strict and balanced.

    MAINWT=<main> python3 rf_climb.py SEEDS STEPS SEED [K N]   SEEDS: 'known' or 'rand' (then K, N)"""
import sys, os, json, random, itertools, collections, time, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rf_lib import Inst
from rf_run import strict_balanced, gen_sets, rand_vals, VMAX


def good_states(I, p, cap=None):
    B = [frozenset([g]) if g is not None else frozenset() for g in p]; c = 1 if I.complete1(B) is not None else 0
    for nb in I.moves(B):
        if cap is not None and c >= cap: break
        if I.complete1(nb) is not None: c += 1
    return c


def score(sets, vals):
    I = Inst(sets, vals); n = I.n; N = I.nu(); starts = set()
    for o in itertools.permutations(range(n)):
        p = I.sd(o)
        if sum(x is not None for x in p) == N: starts.add(p)
    fails = [p for p in starts if I.oc1(p) == 'OC1 fails']
    if not fails:
        return (0, -min(good_states(I, p) for p in starts)), None
    worst = None; wit = None
    for p in fails:
        for u in I.receivers(p):
            for rest in itertools.permutations([i for i in range(n) if i != u]):
                q = I.sd((u,) + rest)
                if sum(x is not None for x in q) != N: continue
                gq = good_states(I, q)
                if worst is None or gq < worst: worst, wit = gq, (p, u, (u,) + rest, q)
    if worst is None: return (1, 0), None    # failing starts without receiver-first max orders
    return (1, -worst), wit


def job(a):
    sets, vals, steps, seed = a; rng = random.Random(seed); sc, wit = score(sets, vals); best = (sc, vals, wit)
    for _ in range(steps):
        v2 = [list(x) for x in vals]; i = rng.randrange(len(sets))
        for _t in range(100):
            y = list(v2[i]); j = rng.randrange(len(y)); y[j] = max(1, min(VMAX * 2, y[j] + rng.choice([-7, -3, -1, 1, 3, 7]) if rng.random() < 0.7 else rng.randint(1, VMAX * 2)))
            if strict_balanced(y): break
        else: continue
        v2[i] = y; sc2, wit2 = score(sets, v2)
        if sc2 >= sc:
            vals, sc, wit = v2, sc2, wit2
            if sc > best[0]: best = (sc, vals, wit)
        if sc == (1, 0) and wit is not None: break
    return seed, sets, best


if __name__ == '__main__':
    mode, STEPS, SEED = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    print('$ python3 kgen/rf/rf_climb.py', *sys.argv[1:], flush=True); t0 = time.time(); rng = random.Random(SEED); tasks = []
    if mode == 'known':
        from rf_known import items
        for r in range(int(os.environ.get('REPS', '4'))):
            for name, sets, vals in items: tasks.append((sets, vals, STEPS, SEED * 10 ** 6 + len(tasks)))
    else:
        K, N, NC = int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
        for c in range(NC):
            sets = gen_sets(N, K, rng); tasks.append((sets, [rand_vals(len(s), rng) for s in sets], STEPS, SEED * 10 ** 6 + c))
    C = collections.Counter()
    with mp.Pool() as pool:
        for seed, sets, (sc, vals, wit) in pool.imap_unordered(job, tasks):
            C['climbs'] += 1; C['best score %s' % (sc,)] += 1
            if sc[0] == 1: print('FAILSTART-BEST', json.dumps({'seed': seed, 'sets': sets, 'vals': vals, 'score': sc, 'witness': wit}), flush=True)
            if sc == (1, 0) and wit is not None: C['RF VIOLATIONS'] += 1; print('RF VIOLATION', json.dumps({'sets': sets, 'vals': vals, 'witness': wit}), flush=True)
    for k in sorted(C): print(C[k], k)
    print('time %.0f s' % (time.time() - t0))
