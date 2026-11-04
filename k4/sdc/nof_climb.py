"""Adversarial hill-climb against Conjecture NOF: minimize the number of working candidates (the plain neediest-first
order, and that order with one agent moved last).  0 = counterexample.

    python3 k4/sdc/nof_climb.py SEED n STEPS ROUNDS"""
import sys, json, random, time
import _paths
from sdclib import Enc
from sdc_orders import sd, completable
from sdc_need import rule_order
from sdc_climb import mutate, start


def count(sets, vals):
    m = 1 + max(max(s) for s in sets); E = Enc(sets, vals, m)
    Y0, pi = rule_order(E, 'need2', False)
    cands = {tuple(Y0)} | {tuple(sd(E, [i for i in pi if i != o] + [o])[0]) for o in pi}
    return sum(1 for Y in cands if completable(E, list(Y)))


if __name__ == '__main__':
    seed, n, steps, rounds = map(int, sys.argv[1:5]); rng = random.Random(seed); t0 = time.time()
    print('$ python3 k4/sdc/nof_climb.py', *sys.argv[1:], flush=True)
    for r in range(rounds):
        sets, vals = start(rng, n); c = count(sets, vals)
        for s in range(steps):
            mu = mutate(sets, vals, rng)
            if mu is None or len(mu[0]) != n: continue
            c2 = count(*mu)
            if c2 <= c or rng.random() < 0.03:
                (sets, vals), c = mu, c2
                if c == 0:
                    print('COUNTEREXAMPLE', json.dumps((sets, vals)), flush=True); break
        print('round', r, 'final', c, 'inst', json.dumps((sets, vals)), 'time %.0f' % (time.time() - t0), flush=True)
