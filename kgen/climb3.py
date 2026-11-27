"""Adversarial hill-climb against OC1 at n = 3, any k (brute force kgen/oc3.c).

Objective (minimized, lexicographic): over the 6 orders, the least number of EFX0 allocations reachable in class KEY
(STRICT: OC1 with chains t >= 1; CODE: OC1 as tested in k4/sdc; FREEOC; MD), then the number of orders attaining it,
then the least CODE count.  0 = a counterexample to KEY, printed with its order and picks.
Mutations: one value +-1..3 (or x2, /2), a value set to 0 or made positive, two values of an agent swapped or made
adjacent (near-tie), a good added or dropped (m stays in [MMIN, MMAX]).

    [CLIMB_K=4] [CLIMB_STRICT=1] python3 kgen/climb3.py SEED ROUNDS STEPS MMIN MMAX [KEY] [start-kind]
CLIMB_K caps the positively valued goods per agent (starts from klim:K); CLIMB_STRICT=1 keeps every agent's positive
values distinct; CLIMB_FIXM=1 keeps m fixed (each round draws m in [MMIN, MMAX]): the raw counts reward fewer goods,
and without it the climbs drift to m = 5."""
import sys, random, json, time, os, multiprocessing as mp
from oc3lib import brute, picks, ORD
from gen3 import gen, strict

KEY = 'STRICT'
KCAP = int(os.environ.get('CLIMB_K', '0'))          # max positively valued goods per agent (0: no cap)
NOTIES = os.environ.get('CLIMB_STRICT', '0') == '1'  # reject profiles with ties among an agent's positive values
FIXM = os.environ.get('CLIMB_FIXM', '0') == '1'      # never add or drop goods (raw counts otherwise reward small m)


def objective(v):
    r = brute(v)
    if r[0]['EFX'] == 0: return (-1, 0, 0), r
    c = [d[KEY] for d in r]; lo = min(c)
    return (lo, c.count(lo), min(d['CODE'] for d in r)), r


def mutate(v, rng, lo, hi):
    v = [list(r) for r in v]; m = len(v[0]); i = rng.randrange(3); g = rng.randrange(m); x = rng.random()
    if x < 0.45: v[i][g] = max(0, v[i][g] + rng.choice([-3, -2, -1, 1, 2, 3]))
    elif x < 0.55: v[i][g] = v[i][g] * 2 if rng.random() < 0.5 else v[i][g] // 2
    elif x < 0.62: v[i][g] = 0 if v[i][g] else rng.randint(1, 30)
    elif x < 0.72:
        h = rng.randrange(m); v[i][g], v[i][h] = v[i][h], v[i][g]
    elif x < 0.82:
        h = rng.randrange(m); v[i][g] = v[i][h] + rng.choice([-1, 1])
        v[i][g] = max(0, v[i][g])
    elif x < 0.91:
        if m >= hi or FIXM: return None
        for r in v: r.append(0)
        for a in range(3):
            if rng.random() < 0.7: v[a][m] = rng.randint(1, 20)
    else:
        if m <= lo or FIXM: return None
        for r in v: r.pop(g)
    m = len(v[0])
    if not all(any(v[a][h] > 0 for a in range(3)) for h in range(m)) or not all(any(r) for r in v): return None
    if KCAP and any(sum(1 for x in r if x > 0) > KCAP for r in v): return None
    if NOTIES and not strict(v): return None
    return v


def run_round(args):
    seed, steps, lo, hi, kind = args
    rng = random.Random(seed)
    kinds = ['general', 'zeros', 'ident', 'junk', 'klim:4', 'klim:6']
    k = kind or rng.choice(kinds); m = rng.randint(lo, hi)
    if KCAP: k = 'klim:%d' % KCAP
    if k.startswith('klim'): m = min(m, 3 * int(k.split(':')[1]))
    v = gen(k, m, rng); c, r = objective(v); best = c; found = None
    for s in range(steps):
        w = mutate(v, rng, lo, hi)
        if w is None: continue
        c2, r2 = objective(w)
        if c2 <= c or rng.random() < 0.02:
            v, c, r = w, c2, r2; best = min(best, c)
            if c[0] <= 0:
                o = min(range(6), key=lambda t: r[t][KEY])
                found = (v, ORD[o], picks(v, ORD[o]), c[0]); break
    return seed, k, c, best, v, found


if __name__ == '__main__':
    seed, rounds, steps, lo, hi = map(int, sys.argv[1:6])
    if len(sys.argv) > 6: KEY = sys.argv[6]
    kind = sys.argv[7] if len(sys.argv) > 7 else None
    print('$ python3 kgen/climb3.py', *sys.argv[1:], flush=True); t0 = time.time()
    tasks = [(seed * 7919 + t, steps, lo, hi, kind) for t in range(rounds)]
    with mp.Pool(os.cpu_count(), initializer=lambda k: globals().__setitem__('KEY', k), initargs=(KEY,)) as pool:
        for s, k, c, best, v, found in pool.imap_unordered(run_round, tasks):
            if found:
                print('COUNTEREXAMPLE', KEY, json.dumps(found[0]), 'order', found[1], 'picks', found[2],
                      '(no EFX0 at all)' if found[3] < 0 else '', flush=True)
            print('round seed', s, 'start', k, 'final', c, 'best', best, 'm', len(v[0]), 'inst', json.dumps(v),
                  'time %.0f' % (time.time() - t0), flush=True)
