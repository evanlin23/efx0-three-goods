"""LSS's Algorithm 2 followed by the flexible sink (lss.flex) on random linear instances with 3-cycles, larger than the
brute force allows (k4/girth.md section 4).  EVIDENCE only.

    python3 k4/girth/lsflex_linear.py SEED SECONDS MAXDEG
Counts, per instance: runs (vertex 0, default labels) where Algorithm 2 + some sink fails; whether a random relabeling
with the same vertex 0 repairs it; whether some vertex 0 works.  Prints every instance where no vertex 0 works with the
default labels and 20 random labelings.
"""
import collections
import random
import sys
import time

from lss import labels, random_labels, flex, triangles, two_cycles
from gen import random_linear, with_values


def main():
    seed, secs, maxdeg = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    C = collections.Counter()
    t0 = time.time()
    print('$ python3 k4/girth/lsflex_linear.py', *sys.argv[1:], flush=True)
    while time.time() - t0 < secs:
        n = rng.randint(4, 16)
        edges = random_linear(n, rng, maxdeg=maxdeg, sizes=rng.choice([(2, 3), (2,), (3,), (2, 3, 4), (3, 4)]),
                              tries=rng.randint(5, 40), private=rng.choice([0, 0.3, 0.6]))
        if not edges:
            continue
        I = with_values(n, edges, rng, vmax=rng.choice([5, 9, 20, 50]), mode=rng.choice(['uniform', 'flat', 'geom']))
        if not triangles(I):
            continue
        assert not two_cycles(I)
        C['instances'] += 1
        some = False
        for z in range(I.n):
            C['runs'] += 1
            if flex(I, labels(I, z))[1]:
                some = True
                continue
            C['runs failing (default labels)'] += 1
            if any(flex(I, random_labels(I, z, rng))[1] for _ in range(20)):
                C['  ... repaired by relabeling, same vertex 0'] += 1
        if not some:
            C['instances: no vertex 0 works (default labels)'] += 1
            if not any(flex(I, random_labels(I, z, rng))[1] for z in range(I.n) for _ in range(20)):
                C['instances: nothing works'] += 1
                print('NOTHING WORKS', I, flush=True)
        if C['instances'] % 2000 == 0:
            print(dict(C), flush=True)
    print('maxdeg', maxdeg, dict(C), flush=True)


if __name__ == '__main__':
    main()
