"""Adversarial climbs at larger k (k4/sdc.md §22): instances with up to K valued goods per agent (balanced, distinct values);
target 'sdc' minimizes the number of extendable serial-dictatorship outcomes (0 refutes SD-C), target 'nof2' the
number of working NOF2 candidates (0 refutes NOF2).  A failure is then reduced toward k = 4.

    python3 k4/sdc/bigk_climb.py sdc|nof2|sdc+|nof2+ SEED n K STEPS ROUNDS
    (a trailing + adds the secondary objective "number of complete EFX0 allocations", capped at 60)"""
import sys, json, random, time, itertools
import _paths
from sdclib import Enc
from sdc_orders import sd, completable
from sdc_need import rule_order
from sdc_climb import count as sdc_count


def nof2_count(sets, vals):
    m = 1 + max(max(s) for s in sets); E = Enc(sets, vals, m); Y, pi = rule_order(E, 'need2', False)
    cands = {tuple(Y)} | {tuple(sd(E, [i for i in pi if i != o] + [o])[0]) for o in pi} | \
        {tuple(sd(E, [i for i in pi if i not in (a, b)] + [a, b])[0]) for a, b in itertools.permutations(pi, 2)}
    return sum(1 for Yc in cands if completable(E, list(Yc)))


def n_efx0(sets, vals, cap=60):
    """number of complete EFX0 allocations (capped), by SAT enumeration with blocking clauses"""
    from pysat.solvers import Cadical153
    m = 1 + max(max(s) for s in sets); E = Enc(sets, vals, m)
    cl = list(E.cl) + [[-E.x[g][E.n]] for g in range(m)]
    S = Cadical153(bootstrap_with=cl); c = 0
    xs = [E.x[g][i] for g in range(m) for i in range(E.n)]
    while c < cap and S.solve():
        mdl = set(l for l in S.get_model() if l > 0)
        S.add_clause([-l for l in xs if l in mdl]); c += 1
    S.delete(); return c


def balanced(V): return max(V) < sum(V) - max(V)


def start(rng, n, K):
    m = rng.randint(n + 2, 2 * n + 2)
    while True:
        sets = [sorted(rng.sample(range(m), rng.randint(3, min(K, m)))) for _ in range(n)]
        if len(set().union(*map(set, sets))) == m: break
    vals = []
    for s in sets:
        while True:
            V = rng.sample(range(1, 40), len(s))
            if balanced(V): break
        vals.append(V)
    return sets, vals


def mutate(sets, vals, rng, K):
    sets = [list(s) for s in sets]; vals = [list(v) for v in vals]
    n = len(sets); m = 1 + max(max(s) for s in sets); i = rng.randrange(n); r = rng.random()
    if r < 0.6:
        k = rng.randrange(len(sets[i])); vals[i][k] = max(1, vals[i][k] + rng.choice([-4, -2, -1, 1, 2, 4]))
    elif r < 0.75:
        a, b = rng.sample(range(len(sets[i])), 2); vals[i][a], vals[i][b] = vals[i][b], vals[i][a]
    elif r < 0.88:
        k = rng.randrange(len(sets[i])); g = rng.randrange(m + 1)
        if g in sets[i]: return None
        sets[i][k] = g
    else:
        if len(sets[i]) >= K or (len(sets[i]) > 3 and rng.random() < 0.5):
            k = rng.randrange(len(sets[i])); sets[i].pop(k); vals[i].pop(k)
        else:
            g = rng.randrange(m + 1)
            if g in sets[i]: return None
            sets[i].append(g); vals[i].append(rng.randint(1, 40))
    if len(sets[i]) < 2 or not balanced(vals[i]) or len(set(vals[i])) < len(vals[i]): return None
    used = sorted(set(g for s in sets for g in s)); ren = {g: k for k, g in enumerate(used)}
    return [[ren[g] for g in s] for s in sets], vals


if __name__ == '__main__':
    target = sys.argv[1]; seed, n, K, steps, rounds = map(int, sys.argv[2:7]); rng = random.Random(seed); t0 = time.time()
    print('$ python3 k4/sdc/bigk_climb.py', *sys.argv[1:], flush=True)
    base = (lambda s, v: sdc_count(s, v, 1 + max(max(x) for x in s), False)) if target.startswith('sdc') else nof2_count
    f = (lambda s, v: (base(s, v), n_efx0(s, v))) if target.endswith('+') else base
    for r in range(rounds):
        sets, vals = start(rng, n, K); c = f(sets, vals)
        for st in range(steps):
            mu = mutate(sets, vals, rng, K)
            if mu is None or len(mu[0]) != n: continue
            c2 = f(*mu)
            if c2 <= c or rng.random() < 0.03:
                (sets, vals), c = mu, c2
                if (c[0] if isinstance(c, tuple) else c) == 0: print('COUNTEREXAMPLE', target, json.dumps((sets, vals)), flush=True); break
        print('round', r, 'final', c if not isinstance(c, tuple) else '%d/%d' % c, 'kmax', max(len(s) for s in sets), json.dumps((sets, vals)), 'time %.0f' % (time.time() - t0), flush=True)
