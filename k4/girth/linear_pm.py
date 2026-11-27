"""The linear case (girth >= 3): Pareto-maximal partial EFX0 orientations and their completions
(k4/girth.md, section 4).  Brute force from the raw definitions (brute.py).  EVIDENCE only.

For random linear hypergraphs with a triangle (degree <= MAXDEG, n <= 7, at most 10 goods), every partial EFX0
orientation is enumerated, and for the Pareto-maximal ones (value vectors) and for the maxima of several potentials:
  PL      the state has an EFX0 completion (unallocated goods added to any bundles)
  PARK    the hypothesis of Lemma PARK holds (every leftover good whose valuers are all envied has a common safe vertex)
  P+S     PARK with slack absorbers (Lemma SLACK): completion by parks plus single-good absorbers
Potentials: SW (sum of values), LEXIMIN, NSW (number of positive values, then sum of logs), PM+NE (Pareto-maximal,
then most non-envied agents), PM+SW.

    python3 k4/girth/linear_pm.py SEED SECONDS MAXDEG [graphs]
Prints a summary line every 500 instances and at the end; every counterexample to PL is printed.
"""
import collections
import math
import random
import sys
import time

from lss import envied, triangles
from gen import random_linear, with_values
from brute import orientations, efx0_partial, completable, park_condition, park_slack


def states(I):
    out = []
    for assign, X in orientations(I):
        if efx0_partial(I, X):
            out.append((tuple(I.val(i, X[i]) for i in range(I.n)), assign, X))
    return out


def main():
    seed, secs, maxdeg = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3])
    graphs = len(sys.argv) > 4
    rng = random.Random(seed)
    C = collections.Counter()
    t0 = time.time()
    print('$ python3 k4/girth/linear_pm.py', *sys.argv[1:], flush=True)

    def summary():
        print('maxdeg %d%s %s' % (maxdeg, ' graphs' if graphs else '', dict(sorted(C.items()))), flush=True)

    while time.time() - t0 < secs:
        n = rng.randint(3, 7)
        sizes = (2,) if graphs else rng.choice([(2, 3), (2,), (3,), (2, 3, 4), (3, 4)])
        edges = random_linear(n, rng, maxdeg=maxdeg, sizes=sizes, tries=rng.randint(3, 12),
                              private=rng.choice([0, 0.3, 0.6]))
        if not edges or len(edges) > 10:
            continue
        sz = 1
        for e in edges:
            sz *= len(e) + 1
        if sz > 60000:
            continue
        I = with_values(n, edges, rng, vmax=rng.choice([5, 9, 20]), mode=rng.choice(['uniform', 'flat', 'geom']))
        if not triangles(I):
            continue
        S = states(I)
        vecs = {s[0] for s in S}
        pm = {v for v in vecs if not any(w != v and all(a >= b for a, b in zip(w, v)) for w in vecs)}
        pms = [s for s in S if s[0] in pm]
        C['instances'] += 1
        C['PM states'] += len(pms)
        memo = {}

        def pk(s):
            if s[1] not in memo:
                memo[s[1]] = park_condition(I, s[1])[0]
            return memo[s[1]]

        allpark = True
        for s in pms:
            if pk(s):
                continue
            allpark = False
            C['PM states without PARK'] += 1
            ps = park_slack(I, s[1]) is not None
            C['  ... completed by PARK+SLACK'] += ps
            comp = ps or completable(I, s[1]) is not None
            C['  ... completable (PL)'] += comp
            if not comp:
                print('PL COUNTEREXAMPLE', I, s[1], flush=True)
            if C['shown'] < 3:
                C['shown'] += 1
                print('PM without PARK:', I, 'state', s[1], 'P+S', ps, flush=True)
        C['instances: every PM parks'] += allpark
        C['instances: some PM parks'] += any(pk(s) for s in pms)
        for name in ('SW', 'LEXIMIN', 'NSW', 'PM+NE', 'PM+SW'):
            if name == 'SW':
                pool, key = S, lambda s: sum(s[0])
            elif name == 'LEXIMIN':
                pool, key = S, lambda s: tuple(sorted(s[0]))
            elif name == 'NSW':
                pool, key = S, lambda s: (sum(1 for x in s[0] if x > 0), sum(math.log(x) for x in s[0] if x > 0))
            elif name == 'PM+NE':
                pool, key = pms, lambda s: sum(1 for i in range(I.n) if not envied(I, s[2], i))
            else:
                pool, key = pms, lambda s: sum(s[0])
            best = max(key(s) for s in pool)
            ok = all(pk(s) for s in pool if key(s) == best)
            C['instances: every %s-max parks' % name] += ok
        if C['instances'] % 500 == 0:
            summary()
    C.pop('shown', None)
    summary()


if __name__ == '__main__':
    main()
