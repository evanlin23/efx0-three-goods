"""Adversarial hill-climb against Conjecture OC (k4/sdc.md §29).  Objective of a profile: over every order whose
serial-dictatorship picks do not extend, the least number of improving chains (de_free.moves, chains only) after which
the bases extend; then how many orders attain it (and 99 if every order's picks extend).  Minimized; 0 = a start that
one chain cannot repair (then the BFS depth is reported).  Mutations as in sdc_climb.py.

    python3 k4/sdc/oc_climb.py SEED N STEPS ROUNDS [dich]
dich: the dichotomy of §29 instead: a start counts as hard when its picks have no one-absorber completion, and a chain
repairs it when the result has a completion with no absorber (every agent at most one junk good; oc_absorb.extends_A).
oc1: Conjecture OC1 instead: one-absorber completions both at the start and after the chain."""
import sys, json, random, time, itertools
import _paths
import de_free as DF
from sdclib import Enc
from sdc_orders import sd
from sdc_climb import mutate, start

DF.CHAIN_ONLY = True
DICH = False
OC1 = False


def objective(sets, vals):
    if DICH or OC1:
        from oc_absorb import extends_A
        ok0 = lambda E, b: extends_A(E, b, 1); ok1 = lambda E, b: extends_A(E, b, 0 if DICH else 1)
    else:
        ok0 = ok1 = DF.extends
    m = 1 + max(max(s) for s in sets); E = Enc(sets, vals, m); res = {}; memo = {}
    for o in itertools.permutations(range(E.n)):
        Y = tuple(sd(E, list(o))[0])
        if Y in res: continue
        base = [-1] * m
        for i, g in enumerate(Y):
            if g is not None: base[g] = i
        base = tuple(base)
        if ok0(E, base): res[Y] = None; continue
        res[Y] = sum(1 for b2 in DF.moves(E, base) if ok1(E, b2))
    hard = [c for c in res.values() if c is not None]
    if not hard: return (99, 0), None
    lo = min(hard)
    return (lo, sum(1 for c in hard if c == lo)), [Y for Y, c in res.items() if c == lo][0]


if __name__ == '__main__':
    seed, n, steps, rounds = map(int, sys.argv[1:5]); rng = random.Random(seed); t0 = time.time()
    DICH = 'dich' in sys.argv[5:]; OC1 = 'oc1' in sys.argv[5:]
    print('$ python3 k4/sdc/oc_climb.py', *sys.argv[1:], flush=True)
    for r in range(rounds):
        sets, vals = start(rng, n); c, Y = objective(sets, vals); best = c
        for s in range(steps):
            mu = mutate(sets, vals, rng)
            if mu is None or len(mu[0]) != n: continue
            c2, Y2 = objective(*mu)
            if c2 <= c or rng.random() < 0.03:
                (sets, vals), c, Y = mu, c2, Y2; best = min(best, c)
                if c[0] == 0:
                    m = 1 + max(max(x) for x in sets); E = Enc(sets, vals, m)
                    base = [-1] * m
                    for i, g in enumerate(Y):
                        if g is not None: base[g] = i
                    print('OC FAILS', json.dumps((sets, vals)), 'picks', Y, 'depth', DF.search(E, tuple(base), {}), flush=True)
                    break
        print('round', r, 'final', c, 'best', best, 'inst', json.dumps((sets, vals)), 'time %.0f' % (time.time() - t0), flush=True)
