"""Adversarial search against RF-exists (the weak form of RF; ksens, 2026-11-27): at every maximum-matching start Y
where OC1 fails, some receiver u and some u-first order whose picks form a maximum matching satisfy OC1.  (The every
form is false: ksens's RF5, replayed in rf5_replay.py.)  Hill climbs on the values, with twins (agents with equal sets
and values, the RF5 mechanism) optionally kept equal under mutation.

Score (larger = closer to a violation of RF-exists): no failing max start: (0, -fewest completable states over max
starts); else (1, -b) with b = the largest number of completable states over all receiver-first max orders of the
failing start that is hardest in this sense; b = 0 means every receiver-first max order fails OC1 (a violation).  A
failing start without receivers, or without receiver-first max orders, is reported separately (RF says nothing there).

    MAINWT=<main> python3 rf_climb2.py known STEPS SEED          seeds: rf_known.items, RF5, the climb-found failures
    python3 rf_climb2.py twins K N NCLIMB STEPS SEED            random strict cores with one pair of twins"""
import sys, os, json, glob, random, itertools, collections, time, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rf_lib import Inst
from rf_run import strict_balanced, gen_sets, rand_vals, VMAX
from rf_climb import good_states


def score(sets, vals):
    I = Inst(sets, vals); n = I.n; N = I.nu(); starts = set()
    for o in itertools.permutations(range(n)):
        p = I.sd(o)
        if sum(x is not None for x in p) == N: starts.add(p)
    fails = [p for p in starts if I.oc1(p) == 'OC1 fails']
    if not fails: return (0, -min(good_states(I, p) for p in starts)), None
    worst = None
    for p in fails:
        rec = I.receivers(p); b = None; info = []
        for u in rec:
            for rest in itertools.permutations([i for i in range(n) if i != u]):
                q = I.sd((u,) + rest)
                if sum(x is not None for x in q) != N: continue
                gq = good_states(I, q); info.append(((u,) + rest, q, gq))
                b = gq if b is None else max(b, gq)
        if b is None: return (2, 0), ('no receiver-first max order', p, rec)
        if worst is None or b < worst[0]: worst = (b, p, rec, info)
    return (1, -worst[0]), worst[1:]


def twins_of(sets, vals):
    return {i: j for i in range(len(sets)) for j in range(len(sets)) if i != j and sets[i] == sets[j] and vals[i] == vals[j]}


def mutate(sets, vals, rng, keep_twins):
    v2 = [list(x) for x in vals]; i = rng.randrange(len(sets)); tw = twins_of(sets, vals)
    for _t in range(100):
        y = list(v2[i]); j = rng.randrange(len(y))
        y[j] = max(1, min(2 * VMAX, y[j] + rng.choice([-7, -3, -1, 1, 3, 7]) if rng.random() < 0.7 else rng.randint(1, 2 * VMAX)))
        if strict_balanced(y): break
    else: return None
    v2[i] = y
    if keep_twins and i in tw and rng.random() < 0.7: v2[tw[i]] = list(y)
    return v2


def job(a):
    sets, vals, steps, seed = a; rng = random.Random(seed); sc, wit = score(sets, vals); best = (sc, vals, wit)
    for _ in range(steps):
        v2 = mutate(sets, vals, rng, True)
        if v2 is None: continue
        sc2, wit2 = score(sets, v2)
        if sc2 >= sc:
            vals, sc, wit = v2, sc2, wit2
            if sc > best[0]: best = (sc, vals, wit)
        if sc[0] == 2 or sc == (1, 0): break
    return seed, sets, best


def twin_instance(k, n, rng):
    sets = gen_sets(n - 1, k, rng); vals = [rand_vals(len(s), rng) for s in sets]; j = rng.randrange(n - 1)
    return sets + [list(sets[j])], vals + [list(vals[j])]


if __name__ == '__main__':
    mode = sys.argv[1]; print('$ python3 kgen/rf/rf_climb2.py', *sys.argv[1:], flush=True); t0 = time.time(); tasks = []
    if mode == 'known':
        STEPS, SEED = int(sys.argv[2]), int(sys.argv[3])
        from rf_known import items
        from rf5_replay import SETS, VALS
        seeds = [(s, v) for nm, s, v in items] + [(SETS, VALS)]
        here = os.path.dirname(os.path.abspath(__file__))
        for fn in sorted(glob.glob(os.path.join(here, '..', '..', 'results', 'kgen_rf', 'rf_climb_k*.log'))):
            for line in open(fn):
                if line.startswith('FAILSTART '):
                    d = json.loads(line.split(' ', 1)[1]); seeds.append((d['sets'], d['vals']))
        for r in range(int(os.environ.get('REPS', '4'))):
            for s, v in seeds: tasks.append((s, v, STEPS, SEED * 10 ** 6 + len(tasks)))
    else:
        K, N, NC, STEPS, SEED = map(int, sys.argv[2:7]); rng = random.Random(SEED)
        for c in range(NC):
            s, v = twin_instance(K, N, rng); tasks.append((s, v, STEPS, SEED * 10 ** 6 + c))
    C = collections.Counter()
    with mp.Pool() as pool:
        for seed, sets, (sc, vals, wit) in pool.imap_unordered(job, tasks):
            C['climbs'] += 1; C['best score %s' % (sc,)] += 1
            if sc[0] >= 1: print('BEST', json.dumps({'seed': seed, 'sets': sets, 'vals': vals, 'score': sc, 'witness': wit}), flush=True)
            if sc == (1, 0): C['RF-exists VIOLATIONS'] += 1; print('RF-EXISTS VIOLATION', json.dumps({'sets': sets, 'vals': vals, 'witness': wit}), flush=True)
            if sc[0] == 2: C['failing start with no receiver-first max order'] += 1; print('NO-RECEIVER-ORDER', json.dumps({'sets': sets, 'vals': vals, 'witness': wit}), flush=True)
    for k in sorted(C): print(C[k], k)
    print('time %.0f s' % (time.time() - t0))
