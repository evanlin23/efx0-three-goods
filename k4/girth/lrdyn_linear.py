"""Conjecture LR-dyn (k4/girth.md section 4): on a linear instance, for every labeling, LSS-ROT's final state is completed
by dynamic parking (lss.park_dynamic).  EVIDENCE only.

    python3 k4/girth/lrdyn_linear.py random|trap SEED SECONDS
random: random linear instances with a 3-cycle (as lssrot_linear.py, n <= 12); trap: instances grown around the trap of
attempts/k4-girth-linear-pl.md (as lssrot_trap.py).  Every vertex 0 with the default and 2 random labelings; every
failing run is printed; static parking is recorded for comparison.
"""
import collections
import random
import sys
import time

from lss import labels, random_labels, lss_rot, park_any_state, park_dynamic, is_efx0, triangles, two_cycles
from gen import random_linear, with_values
from lssrot_trap import grow


def main():
    mode, seed, secs = sys.argv[1], int(sys.argv[2]), float(sys.argv[3])
    rng = random.Random(seed)
    C = collections.Counter()
    t0 = time.time()
    print('$ python3 k4/girth/lrdyn_linear.py', *sys.argv[1:], flush=True)
    while time.time() - t0 < secs:
        if mode == 'trap':
            I = grow(rng)
            if I is None:
                continue
        else:
            n = rng.randint(3, 12)
            e = random_linear(n, rng, sizes=rng.choice([(2, 3), (2,), (3,), (2, 3, 4)]), tries=rng.randint(3, 30),
                              private=rng.choice([0, 0.3, 0.6]))
            if not e:
                continue
            I = with_values(n, e, rng, vmax=rng.choice([5, 9, 20, 50]), mode=rng.choice(['uniform', 'flat', 'geom']))
            if not triangles(I):
                continue
        assert not two_cycles(I)
        C['instances'] += 1
        for z in range(I.n):
            for rep in range(3):
                lab = labels(I, z) if rep == 0 else random_labels(I, z, rng)
                r = lss_rot(I, lab)
                C['runs'] += 1
                Z = park_dynamic(I, r.X, r.U)
                if Z is None:
                    C['FAIL (dynamic)'] += 1
                    print('FAIL', I, 'labels', lab, 'state', [sorted(b) for b in r.X], 'U', sorted(r.U), flush=True)
                else:
                    assert is_efx0(I, Z) and sorted(g for b in Z for g in b) == list(range(I.m))
                if park_any_state(I, r.X, r.U) is None:
                    C['static parking fails'] += 1
        if C['instances'] % 2000 == 0:
            print(dict(C), flush=True)
    print(mode, dict(C), flush=True)


if __name__ == '__main__':
    main()
