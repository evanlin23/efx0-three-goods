"""LSS-ROT + parking (Conjecture LR) on every linear k = 4 core of results/k4_certs_{3,4,5,6}*.json.gz with random strict
profiles (type domains of k4/check4.py), every vertex 0 with the default labels and random labelings.  EVIDENCE only.

    python3 k4/girth/lssrot_cores.py PROFILES_PER_CORE
"""
import collections
import random
import sys

from lss import Inst, labels, random_labels, lss_rot, park_any_state, is_efx0, two_cycles
from sources import cores, domains


def main():
    per = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    rng = random.Random(1)
    print('$ python3 k4/girth/lssrot_cores.py', per)
    for n in (3, 4, 5, 6):
        C = collections.Counter()
        for f, idx, sets, m in cores(n):
            if two_cycles(Inst(sets, [[1] * len(S) for S in sets], m)):
                continue
            C['linear cores'] += 1
            D = domains(sets, m)
            for _ in range(per):
                ds = [rng.choice(d) for d in D]
                I = Inst([sorted(d) for d in ds], [[d[g] for g in sorted(d)] for d in ds], m)
                for z in range(I.n):
                    for rep in range(2):
                        lab = labels(I, z) if rep == 0 else random_labels(I, z, rng)
                        r = lss_rot(I, lab)
                        assert r.first_break is None
                        Z = park_any_state(I, r.X, r.U)
                        C['runs'] += 1
                        if Z is None:
                            C['FAIL'] += 1
                            print('FAIL', f, idx, I, lab, flush=True)
                        else:
                            assert is_efx0(I, Z)
        print('n = %d: %s' % (n, dict(C)), flush=True)


if __name__ == '__main__':
    main()
