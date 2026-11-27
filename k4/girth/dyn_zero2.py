"""Candidate rule (k4/girth.md section 5): if vertex 0 lies on no 2-cycle (shares at most one good with every other
agent), then LSS's Algorithm 2 with the G1 repair + dynamic parking completes for EVERY order of the other agents.
EVIDENCE only.

    python3 k4/girth/dyn_zero2.py cores N SEED SECS | random SEED SECS
Random strict profiles of random cores with n = N (or random degree-<=4 instances with 2-cycles, n <= 8); for every
agent z on no 2-cycle, every labeling with vertex 0 = z (capped at 120 per z).  Plain dynamic parking (no envy-cycle
rotation, no rotations).  Prints every failing run.
"""
import collections
import itertools
import random
import sys
import time

from lss import Inst, labels, lss_dyn_safe, is_efx0, two_cycles
from gen import random_deg4, with_values


def main():
    mode = sys.argv[1]
    seed, secs = int(sys.argv[-2]), float(sys.argv[-1])
    rng = random.Random(seed)
    print('$ python3 k4/girth/dyn_zero2.py', *sys.argv[1:], flush=True)
    C = collections.Counter()
    if mode == 'cores':
        from sources import cores, domains
        allc = cores(int(sys.argv[2]))
    t0 = time.time()
    while time.time() - t0 < secs:
        if mode == 'cores':
            f, idx, sets, m = rng.choice(allc)
            D = domains(sets, m)
            ds = [rng.choice(d) for d in D]
            I = Inst([sorted(d) for d in ds], [[d[g] for g in sorted(d)] for d in ds], m)
        else:
            n = rng.randint(3, 8)
            e = random_deg4(n, rng, tries=rng.randint(4, 30), private=rng.choice([0, 0.3]))
            if not e:
                continue
            I = with_values(n, e, rng, mode=rng.choice(['uniform', 'flat', 'geom']))
            if not two_cycles(I):
                continue
        on2 = {a for x, y, sh in two_cycles(I) for a in (x, y)}
        free = [a for a in range(I.n) if a not in on2]
        C['instances'] += 1
        if not free:
            continue
        C['instances with an agent on no 2-cycle'] += 1
        for z in free:
            nb = I.neighbours(z)
            rest = [a for a in range(I.n) if a != z and a not in nb]
            labs = [labels(I, z, p, q) for p in itertools.permutations(nb) for q in itertools.permutations(rest)]
            if len(labs) > 120:
                labs = rng.sample(labs, 120)
            for lab in labs:
                r, Z = lss_dyn_safe(I, lab)
                C['runs'] += 1
                if Z is None:
                    C['FAIL'] += 1
                    print('FAIL', I, 'labels', lab, flush=True)
                else:
                    assert is_efx0(I, Z)
        if C['instances'] % 2000 == 0:
            print(dict(C), flush=True)
    print('total', dict(C), flush=True)


if __name__ == '__main__':
    main()
