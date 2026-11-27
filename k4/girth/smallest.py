"""Smallest failing configurations of the faithful LSS algorithm, per failure kind (k4/girth.md section 2,
attempts/k4-girth-faithful.md).  Random search over degree-<=4 hypergraphs with small integer values, keeping for each
kind the instance with the fewest (n, m, total value); vertex 0 = agent 0 with the default labels, choices 'max'.

    python3 k4/girth/smallest.py SEED SECONDS
"""
import random
import sys
import time

from lss import lss, labels, classify
from gen import random_deg4, with_values


def main(seed, secs):
    rng = random.Random(seed)
    best = {}
    t0 = time.time()
    while time.time() - t0 < secs:
        n = rng.randint(2, 4)
        edges = random_deg4(n, rng, maxdeg=4, sizes=rng.choice([(2,), (2, 3), (3,)]), tries=rng.randint(2, 6),
                            private=rng.choice([0, 0.3]))
        if not edges:
            continue
        I = with_values(n, edges, rng, vmax=rng.choice([4, 6, 9]))
        r = lss(I, lab=labels(I, 0))
        c = classify(r)
        if c is None:
            continue
        key = (I.n, I.m, sum(sum(d.values()) for d in I.v))
        for kind in c.split('|'):
            if kind not in best or key < best[kind][0]:
                best[kind] = (key, I)
    for kind in sorted(best):
        key, I = best[kind]
        print(kind, 'n=%d m=%d' % key[:2], I)


if __name__ == '__main__':
    main(int(sys.argv[1]), float(sys.argv[2]))
