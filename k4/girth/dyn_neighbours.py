"""Conjecture DYN (k4/girth.md section 5) near the hardest known instances: for every screen instance with 2-cycles
(k4/de4/ss_screen.py: A131, B131, C127, D3, the GM4 family and the suite instances with n <= 5), profiles obtained by
re-drawing the type of one or two agents from its strict core domain (k4/check4.py's representatives).  EVIDENCE only.

    python3 k4/girth/dyn_neighbours.py PER_INSTANCE SEED
Every vertex 0 with the default labels and two random labelings until one run completes; prints every profile on which
none does.
"""
import collections
import random
import sys

from lss import Inst, labels, random_labels, lss_dyn_safe, is_efx0, two_cycles
from sources import screen, domains


def attempt(I, rng):
    for z in range(I.n):
        for rep in range(3):
            lab = labels(I, z) if rep == 0 else random_labels(I, z, rng)
            r, Z = lss_dyn_safe(I, lab)
            if Z is not None:
                assert is_efx0(I, Z) and sorted(g for b in Z for g in b) == list(range(I.m))
                return True
    return False


def main():
    per = int(sys.argv[1]) if len(sys.argv) > 1 else 50
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    print('$ python3 k4/girth/dyn_neighbours.py', *sys.argv[1:], flush=True)
    C = collections.Counter()
    for name, I in screen():
        if not two_cycles(I):
            continue
        sets = [sorted(I.R[i]) for i in range(I.n)]
        try:
            D = domains(sets, I.m)
        except Exception:
            continue
        if any(not d for d in D):
            continue
        base = [{g: I.v[i][g] for g in sets[i]} for i in range(I.n)]
        for _ in range(per):
            ds = [dict(b) for b in base]
            for a in rng.sample(range(I.n), min(I.n, rng.choice([1, 2]))):
                ds[a] = dict(rng.choice(D[a]))
            J = Inst([sorted(d) for d in ds], [[d[g] for g in sorted(d)] for d in ds], I.m)
            C['profiles'] += 1
            ok = attempt(J, rng)
            C['completed'] += ok
            if not ok:
                print('NO RUN COMPLETES (near %s)' % name, J, flush=True)
    print(dict(C), flush=True)


if __name__ == '__main__':
    main()
