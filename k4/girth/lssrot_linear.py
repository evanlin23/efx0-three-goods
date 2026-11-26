"""LSS-ROT on linear instances (k4/girth.md, section 4): LSS's Algorithm 2 interleaved with the Pareto-improving F5/F6
rotations, then the PARK + SLACK completion, else
any parking (every leftover good whose valuers are all envied goes to some non-envied agent; raw EFX0 check).  EVIDENCE only.

    python3 k4/girth/lssrot_linear.py SEED SECONDS MAXDEG [NMAX]
Every vertex 0 with the default labels and 3 random labelings; prints every failing run (instance, labels) and also
checks the final allocation with the raw EFX0 definition and that no step broke EFX0.
"""
import collections
import random
import sys
import time

from lss import labels, random_labels, lss_rot, park_slack_state, park_any_state, is_efx0, triangles, two_cycles
from gen import random_linear, with_values


def main():
    seed, secs, maxdeg = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3])
    nmax = int(sys.argv[4]) if len(sys.argv) > 4 else 16
    rng = random.Random(seed)
    C = collections.Counter()
    t0 = time.time()
    print('$ python3 k4/girth/lssrot_linear.py', *sys.argv[1:], flush=True)
    while time.time() - t0 < secs:
        n = rng.randint(3, nmax)
        edges = random_linear(n, rng, maxdeg=maxdeg, sizes=rng.choice([(2, 3), (2,), (3,), (2, 3, 4), (3, 4)]),
                              tries=rng.randint(3, 40), private=rng.choice([0, 0.3, 0.6]))
        if not edges:
            continue
        I = with_values(n, edges, rng, vmax=rng.choice([5, 9, 20, 50]), mode=rng.choice(['uniform', 'flat', 'geom']))
        if not triangles(I):
            continue
        assert not two_cycles(I)
        C['instances'] += 1
        for z in range(I.n):
            for rep in range(4):
                lab = labels(I, z) if rep == 0 else random_labels(I, z, rng)
                r = lss_rot(I, lab)
                assert r.first_break is None, r.first_break
                C['runs'] += 1
                C['rotations'] += sum(1 for e in r.events if e[0] in ('F5', 'F6'))
                Z = park_slack_state(I, r.X, r.U)
                if Z is None:
                    C['PARK+SLACK fails'] += 1
                    Z = park_any_state(I, r.X, r.U)
                if Z is None:
                    C['FAIL'] += 1
                    print('FAIL', I, 'labels', lab, 'state', [sorted(b) for b in r.X], 'U', sorted(r.U), flush=True)
                else:
                    assert is_efx0(I, Z)
        if C['instances'] % 1000 == 0:
            print(dict(C), flush=True)
    print('maxdeg', maxdeg, dict(C), flush=True)


if __name__ == '__main__':
    main()
