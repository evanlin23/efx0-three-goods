"""Adversarial climb for the plain run's Lemma K deficit (k4/sdc.md §15): maximize Lemma K's deficit (k4/rulef_model.py,
best owner and kept set) of LB4r's state built from the plain neediest-first R1 picks after need-shrinking upgrades.
Instances: sdc_climb's random balanced instances (3 or 4 goods per agent, private goods allowed).  Reports every
instance reaching deficit >= 2, with whether its plain run extends and whether NOF-R1 holds on it.

    python3 k4/sdc/def_climb.py SEED n STEPS ROUNDS"""
import sys, json, random, time
import _paths
from sdclib import Enc
from sdc_orders import sd, completable
from sdc_need import rule_order
from sdc_climb import mutate, start
from blocks4 import M, RM
from nof import nof


def inst_of(sets, vals, m):
    v = [[0] * m for _ in sets]
    for i, (S, V) in enumerate(zip(sets, vals)):
        for g, x in zip(S, V): v[i][g] = x
    return M.Inst(v)


def score(sets, vals):
    m = 1 + max(max(s) for s in sets); E = Enc(sets, vals, m)
    Y, pi = rule_order(E, 'need2', True); inst = inst_of(sets, vals, m)
    base = [-1] * m; pick = [-1] * len(sets)
    for i, g in enumerate(Y):
        if g is not None: base[g] = i; pick[i] = g
    s = (tuple(base), tuple(pick), tuple([False] * len(sets)))
    s, _ = M.up_run(inst, s, 'shrink')
    d = RM.deficit_K(inst, s)
    return (-5 if d == float('-inf') else min(d, 9)), E, Y


if __name__ == '__main__':
    seed, n, steps, rounds = map(int, sys.argv[1:5]); rng = random.Random(seed); t0 = time.time()
    print('$ python3 k4/sdc/def_climb.py', *sys.argv[1:], flush=True)
    for r in range(rounds):
        sets, vals = start(rng, n); c, E, Y = score(sets, vals); best = c
        for st in range(steps):
            mu = mutate(sets, vals, rng)
            if mu is None or len(mu[0]) != n: continue
            c2, E2, Y2 = score(*mu)
            if c2 >= c or rng.random() < 0.03:
                (sets, vals), c, E, Y = mu, c2, E2, Y2
                if c > best:
                    best = c
                    if c >= 2:
                        m = 1 + max(max(s) for s in sets)
                        ok, o, how = nof(sets, vals, m, True)
                        print('DEFICIT', c, 'plain extends', completable(E, Y), 'NOF-R1', ok, how, json.dumps((sets, vals)), flush=True)
                        if not ok: print('NOF-R1 COUNTEREXAMPLE', json.dumps((sets, vals)), flush=True)
        print('round', r, 'final', c, 'best', best, 'time %.0f' % (time.time() - t0), flush=True)
