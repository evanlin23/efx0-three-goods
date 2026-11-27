"""Adversarial hill-climb against Conjecture OC1-H (k4/ttc.md §8): from every order, the picks have a one-absorber
completion, or some improving chain x_0, ..., x_t with t >= 1 has a one-absorber completion whose absorber is its
head x_t (ttclib.extends_owner).  Objective of a profile: over every order whose picks have no one-absorber completion,
the least number of repairing chains of that kind, then how many orders attain it (99 if no order is hard).
Minimized; 0 = a counterexample to OC1-H (then the plain OC1 count of that start is printed too).  Mutations and
starts as in k4/sdc/sdc_climb.py (same as k4/sdc/oc_climb.py).

    python3 k4/ttc/head_climb.py SEED N STEPS ROUNDS [hd] [ends]
hd: Conjecture OC1-HD instead: only chains whose x_0 is dangerous at the start and whose middle agents x_1..x_{t-1}
take no junk count (the head may take junk)."""
import sys, json, random, time, itertools
import ttclib as T
from sdc_climb import mutate, start


ENDS = False    # 'ends': the absorber may be either endpoint of the chain (x_0 or x_t): Conjecture OC1-E / OC1-ED
SHAPE = False   # 'hd': count only chains with x_0 dangerous at the start and no junk for x_1..x_{t-1} (OC1-HD)


def hd_ok(E, base, b2, path, H, D):
    return path[0] in D and all(not H.get(i) for i in range(1, len(path) - 1))


def counts(E, base):
    head = 0; any1 = 0; memo = {}
    D = T.dangerous_set(E, base) if SHAPE else None
    for b2, ds in T.DF.moves(E, base, describe=True, all_desc=True).items():
        heads = set(d[1][-1] for d in ds if d[0] == 'chain' and len(d[1]) > 1
                    and (not SHAPE or hd_ok(E, base, b2, d[1], d[2], D)))
        if T.extends_A(E, b2, 1):
            any1 += 1
            if any(T.extends_owner(E, b2, h) for h in heads):
                head += 1
            elif ENDS and any(T.extends_owner(E, b2, d[1][0]) for d in ds if d[0] == 'chain' and len(d[1]) > 1
                              and (not SHAPE or hd_ok(E, base, b2, d[1], d[2], D))):
                head += 1
    return head, any1


def objective(sets, vals):
    m = 1 + max(max(s) for s in sets); E = T.Enc(sets, vals, m); res = {}
    for o in itertools.permutations(range(E.n)):
        Y = tuple(T.sd(E, list(o))[0])
        if Y in res:
            continue
        base = T.base_of(E, Y)
        if T.extends_A(E, base, 1):
            res[Y] = None; continue
        res[Y] = counts(E, base)
    hard = [c[0] for c in res.values() if c is not None]
    if not hard:
        return (99, 0), None, None
    lo = min(hard)
    Y = [Y for Y, c in res.items() if c is not None and c[0] == lo][0]
    return (lo, sum(1 for c in hard if c == lo)), Y, res[Y]


if __name__ == '__main__':
    seed, n, steps, rounds = map(int, sys.argv[1:5]); rng = random.Random(seed); t0 = time.time()
    SHAPE = 'hd' in sys.argv[5:]; ENDS = 'ends' in sys.argv[5:]
    print('$ python3 k4/ttc/head_climb.py', *sys.argv[1:], flush=True)
    for r in range(rounds):
        sets, vals = start(rng, n); c, Y, cc = objective(sets, vals); best = c
        for s in range(steps):
            mu = mutate(sets, vals, rng)
            if mu is None or len(mu[0]) != n:
                continue
            c2, Y2, cc2 = objective(*mu)
            if c2 <= c or rng.random() < 0.03:
                (sets, vals), c, Y, cc = mu, c2, Y2, cc2; best = min(best, c)
                if c[0] == 0:
                    print('OC1-H FAILS', json.dumps((sets, vals)), 'picks', Y, 'OC1 repairing chains', cc[1], flush=True)
                    break
        print('round', r, 'final', c, 'best', best, 'inst', json.dumps((sets, vals)), 'time %.0f' % (time.time() - t0),
              flush=True)
