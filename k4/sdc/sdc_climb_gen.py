"""Climb against SD-C for general additive instances (every agent may value every good): minimize the number of
SD outcomes (plain orders) that extend; tie-break: maximize the number of SD outcomes."""
import sys, json, random, time, itertools
from sdclib import Enc
from sdc_orders import sd, completable
def score(sets, vals, m):
    E = Enc(sets, vals, m); outs = set(tuple(sd(E, o)[0]) for o in itertools.permutations(range(E.n)))
    ext = sum(1 for Y in outs if completable(E, list(Y)))
    return (ext, -len(outs))
def mutate(sets, vals, m, rng):
    sets = [list(s) for s in sets]; vals = [list(v) for v in vals]
    i = rng.randrange(len(sets)); r = rng.random()
    if r < 0.7:
        k = rng.randrange(len(sets[i])); vals[i][k] = max(1, vals[i][k] + rng.choice([-5, -2, -1, 1, 2, 5]))
    elif r < 0.85 and len(sets[i]) > 1:
        k = rng.randrange(len(sets[i])); sets[i].pop(k); vals[i].pop(k)
    else:
        g = rng.randrange(m)
        if g in sets[i]: return None
        sets[i].append(g); vals[i].append(rng.randint(1, 30))
    if len(set().union(*map(set, sets))) < m: return None
    return sets, vals
if __name__ == '__main__':
    seed, n, m, steps, rounds = map(int, sys.argv[1:6]); rng = random.Random(seed); t0 = time.time()
    for r in range(rounds):
        sets = [list(range(m)) for _ in range(n)]; vals = [[rng.randint(1, 30) for _ in range(m)] for _ in range(n)]
        sc = score(sets, vals, m)
        for st in range(steps):
            mu = mutate(sets, vals, m, rng)
            if mu is None: continue
            sc2 = score(mu[0], mu[1], m)
            if sc2 <= sc or rng.random() < 0.02:
                (sets, vals), sc = mu, sc2
                if sc[0] == 0: print('COUNTEREXAMPLE', json.dumps((sets, vals)), flush=True); break
        print('round', r, 'final', sc, 'inst', json.dumps((sets, vals)), 'time %.0f' % (time.time() - t0), flush=True)
