"""Adversarial hill-climb against OC1 with n agents (n <= 5; brute force kgen/ocn.c).  Objective (minimized): over all
orders, the least number of EFX0 allocations reachable in class KEY (CODE: t >= 0, STRICT: t >= 1), then the number
of orders attaining it (KEY = SDC: the largest number of free completions of the picks over all orders, i.e. SD-C).
m is fixed per round.  0 = counterexample (printed).  Mutations as kgen/climb3.py (no adding
or dropping goods); CLIMB_K caps the positively valued goods per agent, CLIMB_STRICT=1 keeps values distinct.

    [CLIMB_K=4] [CLIMB_STRICT=1] python3 kgen/climb_n.py N_AGENTS SEED ROUNDS STEPS MMIN MMAX [KEY]
CLIMB_START='<json>' CLIMB_KPEN=4: start every round from that instance and minimize first the number of goods valued
beyond 4 per agent (the cap becomes a penalty), then the count; a counterexample needs penalty 0."""
import sys, os, random, json, time, multiprocessing as mp
from ocnlib import brute_n
from hunt_n import gen_n

KCAP = int(os.environ.get('CLIMB_K', '0')); NOTIES = os.environ.get('CLIMB_STRICT', '0') == '1'
START = os.environ.get('CLIMB_START')      # JSON instance to start every round from (then the k cap is a penalty)
KPEN = int(os.environ.get('CLIMB_KPEN', '0'))  # with START: minimize first the goods valued beyond KPEN per agent
KEY = 'CODE'


def excess(v):
    return sum(max(0, sum(1 for x in r if x > 0) - KPEN) for r in v) if KPEN else 0


def objective(v):
    orders, r = brute_n(v)
    if r[0]['EFX'] == 0: return (excess(v), -1, 0), orders, r
    if KEY == 'SDC':     # SD-C: some order's picks extend under the free completion; minimize the best order's count
        c = [d['FREE0'] for d in r]; hi_ = max(c)
        return (excess(v), hi_, c.count(hi_)), orders, r
    c = [d[KEY] for d in r]; lo = min(c)
    return (excess(v), lo, c.count(lo)), orders, r


def ok(v):
    n, m = len(v), len(v[0])
    if not all(any(v[a][g] > 0 for a in range(n)) for g in range(m)) or not all(any(x) for x in v): return False
    if KCAP and any(sum(1 for x in r if x > 0) > KCAP for r in v): return False
    if NOTIES and any(len(set(x for x in r if x > 0)) < sum(1 for x in r if x > 0) for r in v): return False
    return True


def mutate(v, rng):
    v = [list(r) for r in v]; n, m = len(v), len(v[0]); i = rng.randrange(n); g = rng.randrange(m); x = rng.random()
    if x < 0.5: v[i][g] = max(0, v[i][g] + rng.choice([-3, -2, -1, 1, 2, 3]))
    elif x < 0.6: v[i][g] = v[i][g] * 2 if rng.random() < 0.5 else v[i][g] // 2
    elif x < 0.7: v[i][g] = 0 if v[i][g] else rng.randint(1, 30)
    elif x < 0.85:
        h = rng.randrange(m); v[i][g], v[i][h] = v[i][h], v[i][g]
    else:
        h = rng.randrange(m); v[i][g] = max(0, v[i][h] + rng.choice([-1, 1]))
    return v if ok(v) else None


def run_round(args):
    n, seed, steps, lo, hi = args
    rng = random.Random(seed); m = rng.randint(lo, hi)
    kinds = ['klim:%d' % KCAP] if KCAP else ['general', 'zeros', 'ident', 'junk', 'klim:4', 'klim:6']
    if START:
        v = json.loads(START)
    else:
        while True:
            v = gen_n(rng.choice(kinds), n, m, rng)
            if ok(v): break
    c, orders, r = objective(v); best = c; found = None
    for s in range(steps):
        w = mutate(v, rng)
        if w is None: continue
        c2, o2, r2 = objective(w)
        if c2 <= c or rng.random() < 0.02:
            v, c, orders, r = w, c2, o2, r2; best = min(best, c)
            if c[0] == 0 and c[1] <= 0:
                k = 0 if KEY == 'SDC' else min(range(len(r)), key=lambda t: r[t][KEY])
                found = (v, orders[k], r[k]['picks'], c[1]); break
    return seed, c, best, v, found


if __name__ == '__main__':
    n, seed, rounds, steps, lo, hi = map(int, sys.argv[1:7])
    if len(sys.argv) > 7: KEY = sys.argv[7]
    print('$ python3 kgen/climb_n.py', *sys.argv[1:], 'CLIMB_K=%d CLIMB_STRICT=%d' % (KCAP, NOTIES), flush=True)
    t0 = time.time()
    with mp.Pool(os.cpu_count()) as pool:
        for s, c, best, v, found in pool.imap_unordered(run_round, [(n, seed * 7919 + t, steps, lo, hi) for t in range(rounds)]):
            if found:
                print('COUNTEREXAMPLE', KEY, json.dumps(found[0]), 'order', found[1], 'picks', found[2],
                      '(no EFX0 at all)' if found[3] < 0 else '', flush=True)
            print('round seed', s, 'final', c, 'best', best, 'm', len(v[0]), 'inst', json.dumps(v), 'time %.0f' % (time.time() - t0), flush=True)
