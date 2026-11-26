"""Adversarial climb for OC1 inside strict connected k = 4 cores (k4/ttc.md §13).  The OC1 counterexamples of
attempts/k4-ttc-oc1-counterexample.md are not cores; does the pigeonhole (frozen agents with disjoint junk danger
sets, too few unfrozen agents to hold the junk with one absorber) survive the core conditions?

Instances: random incidences (every agent 3 or 4 goods, every good relevant), each agent a random strict balanced
type and ranking (de4lib.random_profile), kept only if k4/c4_verify_H/hcore.py's is_core4 accepts them (degrees 3/4,
strictly balanced, at most d - 2 private goods and p + q < s + t for two, strict (no equal disjoint subset sums),
every good relevant, connected).  Mutations: resample one agent's type and ranking (70%), or replace one of its goods
and resample (30%); a mutation is kept only if the result is still a core.  Score of an instance over a sample of
orders: (hard starts * CAPC - least repairing count) * 1000 + soft signal, where a hard start has no one-absorber
completion (oc_absorb.extends_A), its repairing count is the number of improving moves (de_free additions and
chains) after which the bases have one (capped), and the soft signal counts frozen agents whose junk is worth more
than their pick plus 2 per agent without a pick.  A start with count 0 is printed (an OC1 counterexample inside the
cores; then checked against rings too and against the free completion).

    python3 k4/ttc/core_climb.py N_RUNS ROUNDS ORDERS SEED NMIN NMAX"""
import sys, os, json, random, collections, time, multiprocessing as mp
import ttclib as T
sys.path.insert(0, os.path.join(T.ROOT, 'k4', 'c4_verify_H'))
from hcore import is_core4

CAPC = 30
_cwd = os.getcwd(); os.chdir(T._paths.DE4)
from de4lib import random_profile  # noqa: E402
os.chdir(_cwd)


def vmatrix(sets, vals, m):
    v = [[0] * m for _ in sets]
    for i, (s, vv) in enumerate(zip(sets, vals)):
        for g, x in zip(s, vv):
            v[i][g] = x
    return v


def is_core(sets, vals, m):
    return not is_core4(vmatrix(sets, vals, m))


def gen_core(n, rng, tries=20000):
    for _ in range(tries):
        m = rng.randint(n + 2, 2 * n)
        sets = [sorted(rng.sample(range(m), rng.choice([3, 4, 4]))) for _ in range(n)]
        if len(set().union(*map(set, sets))) != m:
            continue
        vals = random_profile(sets, rng)
        if is_core(sets, vals, m):
            return sets, vals, m
    return None


def mutate(sets, vals, m, rng):
    sets = [list(s) for s in sets]; vals = [list(v) for v in vals]
    i = rng.randrange(len(sets))
    if rng.random() < 0.3:
        j = rng.randrange(len(sets[i])); g = rng.randrange(m)
        if g in sets[i]:
            return None
        sets[i][j] = g; sets[i].sort()
        if len(set().union(*map(set, sets))) < m:
            return None
    vals[i] = random_profile([sets[i]], rng)[0]
    return (sets, vals) if is_core(sets, vals, m) else None


def count(E, base, cap=CAPC):
    seen = set(); c = 0
    for b2 in T.DF.iter_chains(E, base):
        if b2 in seen:
            continue
        seen.add(b2)
        if T.extends_A(E, b2, 1):
            c += 1
            if c >= cap:
                break
    return c


def evaluate(sets, vals, m, ords):
    E = T.Enc(sets, vals, m); hard = 0; least = CAPC; bad = None; done = {}; soft = 0
    for o in ords:
        Y = tuple(T.sd(E, o)[0])
        if Y in done:
            continue
        base = T.base_of(E, Y)
        J = [g for g in range(m) if base[g] < 0]
        for x in T.frozen_set(E, base):
            if T.val(E, x, [g for g in J if E.v[x].get(g, 0) > 0]) > T.val(E, x, [Y[x]]):
                soft += 1
        soft += 2 * sum(1 for y in Y if y is None)
        if T.extends_A(E, base, 1):
            done[Y] = None; continue
        hard += 1; r = count(E, base); done[Y] = r; least = min(least, r)
        if r == 0:
            bad = (o, Y)
    return ((hard * CAPC - least) * 1000 + soft) if hard else soft, hard, least, bad


def run(args):
    n, rounds, norders, seed = args
    rng = random.Random(seed)
    g = gen_core(n, rng)
    if g is None:
        return n, seed, None, None, None, None, []
    sets, vals, m = g
    ords = [list(range(n)), list(range(n))[::-1]]
    while len(ords) < norders:
        o = list(range(n)); rng.shuffle(o); ords.append(o)
    best = evaluate(sets, vals, m, ords); found = []
    for r in range(rounds):
        mu = mutate(sets, vals, m, rng)
        if mu is None:
            continue
        ev = evaluate(mu[0], mu[1], m, ords)
        if ev[3] is not None:
            E = T.Enc(mu[0], mu[1], m); base = T.base_of(E, ev[3][1])
            DFm = T.DF
            DFm.CHAIN_ONLY = False
            rings_ok = any(T.extends_A(E, b2, 1) for b2 in DFm.moves(E, base))
            DFm.CHAIN_ONLY = True
            free = T.DF.extends(E, base)
            found.append((mu[0], mu[1], m, ev[3], rings_ok, free))
        if ev[0] >= best[0]:
            sets, vals = mu; best = ev
    return n, seed, best, sets, vals, m, found


if __name__ == '__main__':
    NR, ROUNDS, ORD, SEED, NMIN, NMAX = map(int, sys.argv[1:7])
    print('$ python3 k4/ttc/core_climb.py', *sys.argv[1:], flush=True)
    t0 = time.time(); C = collections.Counter()
    tasks = [(NMIN + t % (NMAX - NMIN + 1), ROUNDS, ORD, SEED * 1009 + t) for t in range(NR)]
    with mp.Pool(max(1, (os.cpu_count() or 2) - 1)) as pool:
        for n, seed, best, sets, vals, m, found in pool.imap_unordered(run, tasks):
            C['runs n=%d' % n] += 1
            if best is None:
                print('run n=%d seed=%d: no core generated' % (n, seed), flush=True); continue
            print('run n=%d seed=%d score=%d hard=%d least=%d' % (n, seed, best[0], best[1], best[2]),
                  json.dumps((sets, vals)), flush=True)
            for s_, v_, m_, (o, Y), rings_ok, free in found:
                C['OC1 failures inside cores (chains)'] += 1; C['  repaired by a ring'] += rings_ok
                C['  picks have a free completion'] += free
                print('CORE OC1 FAILS', json.dumps({'sets': s_, 'vals': v_, 'm': m_, 'order': o, 'picks': Y,
                                                    'ring repairs': rings_ok, 'free completion': free}), flush=True)
    for k in sorted(C):
        print(k, C[k])
    print('time %.0f s' % (time.time() - t0), flush=True)
