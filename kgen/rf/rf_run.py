"""Test Conjecture RF (rf_lib.py docstring; k4/sdc.md §31 end) at general k on random and hill-climbed strict cores.

Instances (the k = 4 MC2-class rules of k4/sdc/oc1_mc2_rand.gen, with up to k goods per agent): n agents, agent i
values d_i in [3, k] goods, at most one private good each, every shared good valued by >= 2 agents, connected; values
random integers in [1, VMAX], strict (disjoint nonempty subsets of R_i differ in value) and balanced (2 v_i(g) < v_i(R_i)).

For each instance: every order's SD picks; for each distinct maximum-matching pick vector, OC1 (rf_lib.Inst.oc1); at
each failing one, RF: every receiver-first order whose picks are a maximum matching must satisfy OC1.

    python3 rf_run.py rand  K N NINST SEED [DMIN]          random instances
    python3 rf_run.py climb K N NCLIMB STEPS SEED [DMIN]   hill climbs on the values (and occasionally the sets) toward
                                                           failing maximum-matching starts"""
import sys, os, json, random, itertools, collections, time, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rf_lib import Inst

VMAX = 60


def strict_balanced(x):
    if 2 * max(x) >= sum(x): return False
    seen = {}
    for r in range(1, len(x) + 1):
        for T in itertools.combinations(range(len(x)), r):
            s = sum(x[k] for k in T); seen.setdefault(s, []).append(set(T))
    return all(a & b for L in seen.values() for a, b in itertools.combinations(L, 2))


def rand_vals(d, rng):
    while True:
        x = [rng.randint(1, VMAX) for _ in range(d)]
        if strict_balanced(x): return x


def gen_sets(n, k, rng, dmin=3):
    while True:
        d = [rng.randint(dmin, k) for _ in range(n)]; p = [rng.choice([0, 1]) for _ in range(n)]
        slots = sum(di - pi for di, pi in zip(d, p))
        if slots // 2 < max(2, n - 1): continue
        s = rng.randint(max(2, n - 1), slots // 2)
        if any(d[i] - p[i] > s for i in range(n)): continue
        sh = [sorted(rng.sample(range(s), d[i] - p[i])) for i in range(n)]
        deg = collections.Counter(g for x in sh for g in x)
        if any(deg[g] < 2 for g in range(s)): continue
        comp = {0}; grow = True
        while grow:
            grow = False
            for j in range(n):
                if j not in comp and any(set(sh[j]) & set(sh[i]) for i in comp): comp.add(j); grow = True
        if len(comp) < n: continue
        sets = []; nxt = s
        for i in range(n):
            sets.append(sh[i] + ([nxt] if p[i] else [])); nxt += p[i]
        return sets


def analyse(sets, vals, detail=False):
    """returns Counter of outcomes, list of RF violations, list of failing max starts (with their RF data)"""
    I = Inst(sets, vals); n = I.n; N = I.nu(); C = collections.Counter(); seen = {}; viol = []; fails = []
    for o in itertools.permutations(range(n)):
        p = I.sd(o)
        if p in seen: continue
        if sum(x is not None for x in p) != N: seen[p] = 'non-max'; continue
        r = I.oc1(p); seen[p] = r; C['max starts: ' + r] += 1
        if r == 'OC1 fails':
            rec, out, nonmax = I.rf(p, N)
            C['failing max starts with %d receivers' % len(rec)] += 1
            bad = [(o2, p2) for o2, p2, r2 in out if r2 == 'OC1 fails']
            C['RF holds at a failing start: %s' % (not bad)] += 1
            C['receiver-first non-max orders'] += nonmax
            fails.append((p, rec, len(out), bad))
            if bad: viol.append((p, rec, bad))
    return C, viol, fails


def hardness(sets, vals):
    """climb score: (number of failing max starts, -fewest repairing states over max starts that need a move)"""
    I = Inst(sets, vals); n = I.n; N = I.nu(); seen = set(); nf = 0; best = 10 ** 9
    for o in itertools.permutations(range(n)):
        p = I.sd(o)
        if p in seen or sum(x is not None for x in p) != N: continue
        seen.add(p); B = [frozenset([g]) if g is not None else frozenset() for g in p]
        if I.complete1(B) is not None: continue
        rep = sum(1 for nb in I.moves(B) if I.complete1(nb) is not None)
        if rep == 0: nf += 1
        best = min(best, rep)
    return (nf, -best if best < 10 ** 9 else -10 ** 6)


def job_rand(a):
    k, n, seed, dmin = a; rng = random.Random(seed); sets = gen_sets(n, k, rng, dmin); vals = [rand_vals(len(s), rng) for s in sets]
    C, viol, fails = analyse(sets, vals); return seed, sets, vals, C, viol, fails


def job_climb(a):
    k, n, steps, seed, dmin = a; rng = random.Random(seed)
    sets = gen_sets(n, k, rng, dmin); vals = [rand_vals(len(s), rng) for s in sets]; sc = hardness(sets, vals)
    for _ in range(steps):
        if rng.random() < 0.05:
            s2 = gen_sets(n, k, rng, dmin); v2 = [rand_vals(len(s), rng) for s in s2]
        else:
            s2 = sets; v2 = [list(x) for x in vals]; i = rng.randrange(n)
            while True:
                y = list(v2[i]); y[rng.randrange(len(y))] = rng.randint(1, VMAX)
                if strict_balanced(y): break
            v2[i] = y
        sc2 = hardness(s2, v2)
        if sc2 >= sc: sets, vals, sc = s2, v2, sc2
    C, viol, fails = analyse(sets, vals); return seed, sets, vals, C, viol, fails, sc


if __name__ == '__main__':
    mode, k, n = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    print('$ python3 kgen/rf/rf_run.py', *sys.argv[1:], flush=True); t0 = time.time(); T = collections.Counter(); shown = 0
    if mode == 'rand':
        NI, SEED = int(sys.argv[4]), int(sys.argv[5]); dmin = int(sys.argv[6]) if len(sys.argv) > 6 else 3
        tasks = [(k, n, SEED * 10 ** 6 + i, dmin) for i in range(NI)]; fn = job_rand
    else:
        NC, STEPS, SEED = int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]); dmin = int(sys.argv[7]) if len(sys.argv) > 7 else 3
        tasks = [(k, n, STEPS, SEED * 10 ** 6 + i, dmin) for i in range(NC)]; fn = job_climb
    with mp.Pool() as pool:
        for res in pool.imap_unordered(fn, tasks):
            seed, sets, vals, C, viol, fails = res[:6]; T.update(C); T['instances'] += 1
            for p, rec, nout, bad in fails:
                print('FAILSTART', json.dumps({'seed': seed, 'sets': sets, 'vals': vals, 'picks': p, 'receivers': rec, 'rf_orders': nout, 'rf_bad': bad}), flush=True)
            if viol: T['instances violating RF'] += 1; print('RF VIOLATION', json.dumps({'seed': seed, 'sets': sets, 'vals': vals, 'viol': viol}), flush=True)
    for key in sorted(T): print(T[key], key)
    print('time %.0f s' % (time.time() - t0))
