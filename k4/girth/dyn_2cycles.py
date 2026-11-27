"""LSS's Algorithm 2 with the G1 repair (lss.alg2_safe; PLAIN=1 for the unrepaired one) followed by dynamic parking (lss.park_dynamic: goods go one at a time to agents non-envied at that
moment, raw EFX0 after each step) on instances WITH 2-cycles (k4/girth.md section 5).  EVIDENCE only.

    python3 k4/girth/dyn_2cycles.py PROFILES_PER_CORE
Per instance: every vertex 0 with the default labels and 2 random labelings.  Counts runs where Algorithm 2 itself broke
EFX0 (G1), runs completed, and instances where no run completed (printed).
"""
import collections
import os
import random
import sys

from lss import Inst, labels, random_labels, lss_dyn, lss_dyn_safe, is_efx0, two_cycles
SAFE = os.environ.get('PLAIN') is None      # PLAIN=1: Algorithm 2 without the G1 repair
from sources import screen, suite, cores, domains


def run(name, insts, rng, show=3):
    C = collections.Counter()
    for I in insts:
        some = False
        for z in range(I.n):
            for rep in range(3):
                lab = labels(I, z) if rep == 0 else random_labels(I, z, rng)
                r, Z = (lss_dyn_safe if SAFE else lss_dyn)(I, lab)
                C['runs'] += 1
                if r.first_break is not None and not is_efx0(I, r.X):
                    C['Algorithm 2 broke EFX0 (G1)'] += 1
                if Z is not None:
                    assert is_efx0(I, Z)
                    C['completed'] += 1
                    some = True
        C['instances'] += 1
        C['instances completed by some run'] += some
        if not some and show:
            show -= 1
            print('  no run completes:', I, flush=True)
    print('%-32s %s' % (name, dict(C)), flush=True)


def main():
    per = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    rng = random.Random(3)
    print('$ python3 k4/girth/dyn_2cycles.py', per)
    run('screen', [I for _, I in screen() if two_cycles(I)], rng)
    run('suite', [I for _, I in suite() if two_cycles(I)], rng)
    for n in (2, 3):
        L = []
        for f, idx, sets, m in cores(n):
            D = domains(sets, m)
            for _ in range(per * (5 if n == 2 else 1)):
                ds = [rng.choice(d) for d in D]
                L.append(Inst([sorted(d) for d in ds], [[d[g] for g in sorted(d)] for d in ds], m))
        run('k=4 cores n=%d, random profiles' % n, L, rng)


if __name__ == '__main__':
    main()
