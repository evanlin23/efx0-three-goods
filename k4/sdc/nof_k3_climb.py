"""NOF and NO at k = 3 (k4/sdc.md §18): adversarial climb over instances in which every agent values exactly three goods
(balanced, distinct values), minimizing the number of working NOF candidates (the plain neediest-first order, which at
k = 3 is an R1 run of LB's Phase 1, or it with one agent moved last).  0 = counterexample to NOF at k = 3.

    python3 k4/sdc/nof_k3_climb.py SEED n STEPS ROUNDS"""
import sys, json, random, time
import _paths
from sdclib import Enc
from sdc_orders import sd, completable
from sdc_need import rule_order
from sdc_climb import mutate, balanced


def count(sets, vals):
    m = 1 + max(max(s) for s in sets); E = Enc(sets, vals, m)
    Y0, pi = rule_order(E, 'need2', False)
    cands = {tuple(Y0)} | {tuple(sd(E, [i for i in pi if i != o] + [o])[0]) for o in pi}
    return sum(1 for Y in cands if completable(E, list(Y)))


def start3(rng, n):
    m = rng.randint(n + 2, 2 * n)
    while True:
        sets = [sorted(rng.sample(range(m), 3)) for _ in range(n)]
        if len(set().union(*map(set, sets))) == m: break
    vals = []
    for s in sets:
        while True:
            V = rng.sample(range(1, 40), 3)
            if balanced(V): break
        vals.append(V)
    return sets, vals


if __name__ == '__main__':
    seed, n, steps, rounds = map(int, sys.argv[1:5]); rng = random.Random(seed); t0 = time.time()
    print('$ python3 k4/sdc/nof_k3_climb.py', *sys.argv[1:], flush=True)
    for r in range(rounds):
        sets, vals = start3(rng, n); c = count(sets, vals)
        for s in range(steps):
            mu = mutate(sets, vals, rng)
            if mu is None or len(mu[0]) != n or any(len(x) != 3 for x in mu[0]): continue
            c2 = count(*mu)
            if c2 <= c or rng.random() < 0.03:
                (sets, vals), c = mu, c2
                if c == 0:
                    print('COUNTEREXAMPLE', json.dumps((sets, vals)), flush=True); break
        print('round', r, 'final', c, 'inst', json.dumps((sets, vals)), 'time %.0f' % (time.time() - t0), flush=True)
