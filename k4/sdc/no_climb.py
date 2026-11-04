"""Adversarial hill-climb against Conjecture NO: minimize the number of owners o for which "neediest first, o last"
extends (0 = counterexample).  Mutations as sdc_climb.py (values, swaps, goods moved, goods added or dropped).

    python3 k4/sdc/no_climb.py SEED n STEPS ROUNDS"""
import sys, json, random, time
import _paths
from sdclib import Enc
from sdc_orders import completable
from sdc_need_owner import order_with_last
from sdc_climb import mutate, start


def count(sets, vals):
    m = 1 + max(max(s) for s in sets); E = Enc(sets, vals, m)
    return sum(1 for o in range(E.n) if completable(E, order_with_last(E, 'need2', False, o)[0]))


if __name__ == '__main__':
    seed, n, steps, rounds = map(int, sys.argv[1:5]); rng = random.Random(seed); t0 = time.time()
    print('$ python3 k4/sdc/no_climb.py', *sys.argv[1:], flush=True)
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
