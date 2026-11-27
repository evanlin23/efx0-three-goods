"""Adversarial climb against OC1^max (k4/attack_log.md 21:56) on strict connected k = 4 cores.  OC1^max: for every
serial-dictatorship order whose picks form a maximum matching of the agent / relevant-good graph, the picks have a
one-absorber completion, or one official move (chain or ring, k4/sdc.md §29) leads to a state with one.

State: a strict connected k = 4 core (conditions (C1)-(C5) of K4.CORE, strictness, connectivity; MC2=1 also forbids
two private goods).  Score over the distinct pick vectors of the maximum-matching orders (each weighted once):
    1000 * (vectors that fail OC1)  +  sum over vectors needing a move of (CAP - repairing states, capped)  +  danger
where danger counts frozen pick holders whose junk is worth more than their pick.  Mutations: one value +-1..3, or one
relevant good of one agent moved to another good (or to a fresh good); rejected unless the result is again a strict
connected core.  Accept if the score does not drop.  Coordinator's own code (oc1_mc2_rand.Inst).

    python3 k4/sdc/oc1max_climb.py RUNS STEPS SEED seedB|rand NMIN NMAX [MC2]

With LOOSE=1 the core conditions are dropped (any instance with 2..4 goods per agent and distinct values per agent),
to test whether OC1^max needs the core restriction at all."""
import sys, os, json, random, itertools, collections, time, multiprocessing as mp
from oc1_mc2_rand import Inst, gen
from oc1_max_orders import nu

CAP = 8
B_SETS = [[0, 2, 3, 1], [6, 4, 5, 9], [1, 2, 3, 9], [1, 6, 7, 8], [3, 6, 9], [1, 3, 6, 9]]
B_VALS = [[6, 14, 16, 12], [4, 18, 12, 28], [28, 4, 16, 21], [16, 14, 12, 6], [28, 8, 24], [20, 30, 8, 4]]


LOOSE = os.environ.get('LOOSE') == '1'   # any instance: 2..4 goods per agent, values distinct per agent, every good relevant


def is_core(sets, vals, mc2):
    n = len(sets); goods = sorted(set().union(*map(set, sets)))
    if goods != list(range(len(goods))): return False
    if LOOSE:
        return all(2 <= len(s) <= 4 and len(set(s)) == len(s) and len(set(x)) == len(x) for s, x in zip(sets, vals))
    R = [set(s) for s in sets]
    for i in range(n):
        d = len(sets[i]); x = vals[i]
        if d not in (3, 4) or len(set(sets[i])) != d: return False
        if 2 * max(x) >= sum(x): return False
        P = [k for k, g in enumerate(sets[i]) if all(g not in R[j] for j in range(n) if j != i)]
        if len(P) + 2 > d or (mc2 and len(P) > 1): return False
        if len(P) == 2 and not sum(x[k] for k in P) < sum(x) - sum(x[k] for k in P): return False
        sums = collections.defaultdict(list)
        for r in range(1, d + 1):
            for T in itertools.combinations(range(d), r): sums[sum(x[k] for k in T)].append(set(T))
        for L in sums.values():
            if any(not (a & b) for a, b in itertools.combinations(L, 2)): return False
    comp = {0}; grow = True
    while grow:
        grow = False
        for j in range(n):
            if j not in comp and any(R[j] & R[i] for i in comp): comp.add(j); grow = True
    return len(comp) == n


def evaluate(sets, vals):
    I = Inst(sets, vals); N = nu(I)
    pv = {I.sd(o) for o in itertools.permutations(range(I.n))}
    pv = [p for p in pv if sum(x is not None for x in p) == N]
    fails = []; soft = 0; danger = 0
    for p in pv:
        base = [[g] if g is not None else [] for g in p]
        J = [g for g in range(I.m) if g not in p]
        for x, gx in enumerate(p):
            if gx is not None and any(i != x and I.v[i].get(gx, 0) > I.V(i, base[i]) for i in range(I.n)) \
                    and I.V(x, J) > I.v[x][gx]: danger += 1
        if I.one_absorber(base): continue
        rep = 0
        for st in I.moves(base):
            if I.one_absorber([list(b) for b in st]):
                rep += 1
                if rep >= CAP: break
        if rep == 0: fails.append(p)
        soft += CAP - rep
    return 1000 * len(fails) + 10 * soft + danger, fails


def mutate(sets, vals, rng):
    sets = [list(s) for s in sets]; vals = [list(v) for v in vals]
    i = rng.randrange(len(sets)); m = 1 + max(max(s) for s in sets)
    if rng.random() < 0.75:
        k = rng.randrange(len(vals[i])); vals[i][k] = max(1, vals[i][k] + rng.choice([-3, -2, -1, 1, 2, 3]))
    else:
        k = rng.randrange(len(sets[i])); g = rng.randrange(m + 1)
        if g in sets[i]: return None
        sets[i][k] = g
        used = sorted(set().union(*map(set, sets))); ren = {g: t for t, g in enumerate(used)}
        sets = [[ren[g] for g in s] for s in sets]
    return sets, vals


def run(args):
    steps, seed, start, n, mc2 = args
    rng = random.Random(seed)
    if start == 'seedB': sets, vals = [list(s) for s in B_SETS], [list(v) for v in B_VALS]
    else:
        while True:
            sets, vals = gen(n, rng)
            if is_core(sets, vals, mc2): break
    while not is_core(sets, vals, mc2):          # seedB with MC2: walk into the class
        mu = mutate(sets, vals, rng)
        if mu: sets, vals = mu
    best, fails = evaluate(sets, vals); found = []
    for _ in range(steps):
        mu = mutate(sets, vals, rng)
        if mu is None or not is_core(*mu, mc2): continue
        sc, fl = evaluate(*mu)
        if fl: found.append((mu[0], mu[1], fl))
        if sc >= best: (sets, vals), best = mu, sc
    return seed, best, sets, vals, found


if __name__ == '__main__':
    RUNS, STEPS, SEED = map(int, sys.argv[1:4]); START = sys.argv[4]; NMIN, NMAX = map(int, sys.argv[5:7])
    MC2 = len(sys.argv) > 7 and sys.argv[7] == 'MC2'
    print('$ python3 k4/sdc/oc1max_climb.py', *sys.argv[1:], flush=True)
    t0 = time.time(); C = collections.Counter()
    tasks = [(STEPS, SEED * 7919 + t, START, NMIN + t % (NMAX - NMIN + 1), MC2) for t in range(RUNS)]
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for seed, best, sets, vals, found in pool.imap_unordered(run, tasks):
            C['runs'] += 1
            print('run seed=%d score=%d %s' % (seed, best, json.dumps((sets, vals))), flush=True)
            for s2, v2, fl in found:
                C['OC1^max counterexamples'] += 1
                print('OC1max FAILS', json.dumps({'sets': s2, 'vals': v2, 'picks': fl}), flush=True)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
