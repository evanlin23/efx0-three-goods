"""Climb minimizing the fraction of SD outcomes (distinct pick vectors over all orders, R1 or plain) that extend."""
import sys, json, random, time, itertools
from sdclib import Enc
from sdc_orders import sd, completable
from sdc_climb import mutate, start
def frac(sets, vals, r1):
    m = 1 + max(max(s) for s in sets); E = Enc(sets, vals, m)
    outs = set()
    for order in itertools.permutations(range(E.n)):
        outs.add(tuple(sd(E, order, r1)[0]))
    ext = sum(1 for Y in outs if completable(E, list(Y)))
    return ext / len(outs), ext, len(outs)
if __name__ == '__main__':
    seed, n, steps, rounds, r1 = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5] == 'r1'
    rng = random.Random(seed); t0 = time.time()
    for r in range(rounds):
        sets, vals = start(rng, n); f = frac(sets, vals, r1)
        for st in range(steps):
            mu = mutate(sets, vals, rng)
            if mu is None or len(mu[0]) != n: continue
            f2 = frac(mu[0], mu[1], r1)
            if (f2[0], -f2[2]) <= (f[0], -f[2]) or rng.random() < 0.02:
                (sets, vals), f = mu, f2
                if f[1] == 0: print('COUNTEREXAMPLE', json.dumps((sets, vals)), flush=True); break
        print('round', r, 'final', f, 'inst', json.dumps((sets, vals)), 'time %.0f' % (time.time() - t0), flush=True)
