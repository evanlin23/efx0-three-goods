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

    python3 k4/ttc/core_climb.py N_RUNS ROUNDS ORDERS SEED NMIN NMAX [free] [seeded] [seed=FILE] [mc2] [r1] [max]
max: only orders whose picks form a maximum matching (the coordinator's OC1^max) are scored, sampled per evaluation;
r1: the serial dictatorships use R1 priority (LB's Phase 1; the order breaks ties), i.e. SD-C-R1's orders;
mc2: every instance must also have no agent with two private goods (the class of K4.MC2, CERTIFIED: a minimal
counterexample to TARGET4 has none); seed=FILE: the seed instance for 'seeded' (default oc1_core_candidate.json).
free: Conjecture OC (free completion after at most one move) instead of OC1; seeded: every run starts from the OC1
core counterexample (n = 5).  With 'free', a printed failure is a start that no move repairs even with a free
completion (an OC counterexample inside the cores); 'ring repairs' and 'free completion' are then reported for it."""
import sys, os, json, random, collections, time, multiprocessing as mp
import ttclib as T
sys.path.insert(0, os.path.join(T.ROOT, 'k4', 'c4_verify_H'))
from hcore import is_core4

CAPC = 30
SEEDFILE = 'oc1_core_candidate.json'   # seed=FILE (under results/k4_ttc/) for 'seeded'
FREE = False     # 'free': Conjecture OC instead (free completion, any number of absorbers; de_free.extends)
SEEDED = False   # 'seeded': start every run from the core counterexample to OC1 (results/k4_ttc/oc1_core_candidate.json)
_cwd = os.getcwd(); os.chdir(T._paths.DE4)
from de4lib import random_profile  # noqa: E402
os.chdir(_cwd)


def vmatrix(sets, vals, m):
    v = [[0] * m for _ in sets]
    for i, (s, vv) in enumerate(zip(sets, vals)):
        for g, x in zip(s, vv):
            v[i][g] = x
    return v


MAXM = False    # 'max': score only orders whose picks form a maximum matching of the agent / relevant-good graph
R1 = False      # 'r1': evaluate the orders with R1 priority (sdc_orders.sd(..., r1=True)): OC1 for R1-priority orders
MC2 = False     # 'mc2': also require that no agent has two private goods (the K4.MC2 class)


def two_private(sets):
    import collections
    cnt = collections.Counter(g for s in sets for g in s)
    return any(sum(1 for g in s if cnt[g] == 1) >= 2 for s in sets)


def is_core(sets, vals, m):
    if MC2 and two_private(sets):
        return False
    if DEFICIENT and nu(sets) >= len(sets):
        return False
    return not is_core4(vmatrix(sets, vals, m))


GEN = 'plain'   # gen=deficient: cores with nu < n (a planted Hall-deficient group); gen=dense: m in [2n, 3n]
DEFICIENT = False  # with gen=deficient, every mutation must keep nu < n


def plant(n, m, rng):
    """sets with a Hall-deficient group: s = 4 agents on 3 common goods, or 5 agents on 4 goods (3 or 4 each)"""
    s = rng.choice([4, 5]); G = rng.sample(range(m), s - 1)
    sets = [sorted(G) if s == 4 else sorted(rng.sample(G, rng.choice([3, 4]))) for _ in range(s)]
    sets += [sorted(rng.sample(range(m), rng.choice([3, 4, 4]))) for _ in range(n - s)]
    return sets


def gen_core(n, rng, tries=20000):
    for _ in range(tries):
        if GEN == 'dense':
            m = rng.randint(2 * n, 3 * n)
        else:
            m = rng.randint(n + 2, 2 * n)
        if GEN == 'deficient':
            sets = plant(n, m, rng)
            if nu(sets) >= n:
                continue
        else:
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


def ok(E, b):
    return T.DF.extends(E, b) if FREE else T.extends_A(E, b, 1)


def nu(sets):
    """size of a maximum matching of agents to relevant goods"""
    import networkx as nx
    G = nx.Graph(); A = [('a', i) for i in range(len(sets))]
    G.add_nodes_from(A)
    for i, s in enumerate(sets):
        for g in s:
            G.add_edge(('a', i), ('g', g))
    return len(nx.bipartite.maximum_matching(G, top_nodes=A)) // 2


def max_orders(sets, vals, m, rng, k, tries=None):
    """up to k orders whose serial-dictatorship picks are a maximum matching (identity and reverse first, then
    random), found by sampling; such orders exist (Abraham et al. 2004, Thm 1 and Lemma 1 of §6)"""
    E = T.Enc(sets, vals, m); n = len(sets); target = nu(sets); out = []
    cands = [list(range(n)), list(range(n))[::-1]]
    for _ in range(tries or 20 * k):
        o = list(range(n)); rng.shuffle(o); cands.append(o)
    for o in cands:
        Y = T.sd(E, o, R1)[0]
        if sum(1 for y in Y if y is not None) == target:
            out.append(o)
            if len(out) >= k:
                break
    return out


def count(E, base, cap=CAPC):
    seen = set(); c = 0
    for b2 in T.DF.iter_chains(E, base):
        if b2 in seen:
            continue
        seen.add(b2)
        if ok(E, b2):
            c += 1
            if c >= cap:
                break
    return c


def evaluate(sets, vals, m, ords):
    if MAXM:
        ords = max_orders(sets, vals, m, random.Random(len(ords) * 7919 + sum(map(sum, vals))), len(ords))
    E = T.Enc(sets, vals, m); hard = 0; least = CAPC; bad = None; done = {}; soft = 0
    for o in ords:
        Y = tuple(T.sd(E, o, R1)[0])
        if Y in done:
            continue
        base = T.base_of(E, Y)
        J = [g for g in range(m) if base[g] < 0]
        for x in T.frozen_set(E, base):
            if T.val(E, x, [g for g in J if E.v[x].get(g, 0) > 0]) > T.val(E, x, [Y[x]]):
                soft += 1
        soft += 2 * sum(1 for y in Y if y is None)
        if ok(E, base):
            done[Y] = None; continue
        hard += 1; r = count(E, base); done[Y] = r; least = min(least, r)
        if r == 0:
            bad = (o, Y)
    return ((hard * CAPC - least) * 1000 + soft) if hard else soft, hard, least, bad


def run(args):
    n, rounds, norders, seed = args
    rng = random.Random(seed)
    if SEEDED:
        d = json.load(open(os.path.join(T.ROOT, 'results', 'k4_ttc', SEEDFILE)))[0]
        g = ([list(x) for x in d['sets']], [list(x) for x in d['vals']], d['m']); n = len(g[0])
    else:
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
            rings_ok = any(ok(E, b2) for b2 in DFm.moves(E, base))
            DFm.CHAIN_ONLY = True
            free = T.DF.extends(E, base)
            pk = T.extends_A_pickless(E, base, 1) or any(T.extends_A_pickless(E, b2, 1) for b2 in DFm.iter_chains(E, base))
            found.append((mu[0], mu[1], m, ev[3], rings_ok, free, pk))
        if ev[0] >= best[0]:
            sets, vals = mu; best = ev
    return n, seed, best, sets, vals, m, found


if __name__ == '__main__':
    NR, ROUNDS, ORD, SEED, NMIN, NMAX = map(int, sys.argv[1:7])
    FREE = 'free' in sys.argv[7:]; SEEDED = 'seeded' in sys.argv[7:]; MC2 = 'mc2' in sys.argv[7:]; R1 = 'r1' in sys.argv[7:]
    MAXM = 'max' in sys.argv[7:]
    for a in sys.argv[7:]:
        if a.startswith('gen='):
            GEN = a[4:]
    DEFICIENT = GEN == 'deficient'
    for a in sys.argv[7:]:
        if a.startswith('seed='):
            SEEDFILE = a[5:]
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
            for s_, v_, m_, (o, Y), rings_ok, free, pk in found:
                C['OC1 failures inside cores (chains)'] += 1; C['  repaired by a ring'] += rings_ok
                C['  picks have a free completion'] += free; C['  OC1-p holds (<= 1 move)'] += pk
                print('CORE OC1 FAILS', json.dumps({'sets': s_, 'vals': v_, 'm': m_, 'order': o, 'picks': Y,
                                                    'ring repairs': rings_ok, 'free completion': free,
                                                    'OC1-p': pk, 'two private goods': two_private(s_)}), flush=True)
    for k in sorted(C):
        print(k, C[k])
    print('time %.0f s' % (time.time() - t0), flush=True)
