"""LSS's Algorithm 2 with the G1 repair (lss.alg2_safe; PLAIN=1 for the unrepaired one) + dynamic parking (Conjecture DYN, k4/girth.md section 5) on k = 4 cores with n = 4 or 5 (random strict
profiles of random cores of results/k4_certs_{4,5}_*.json.gz) and on random degree-<=4 instances with 2-cycles.  EVIDENCE only.

    python3 k4/girth/dyn_more.py MODE SEED SECONDS        MODE = cores4 | cores5 | random
"""
import collections
import os
import random
import sys
import time

from lss import Inst, labels, random_labels, lss_dyn, lss_dyn_safe, is_efx0, two_cycles
from gen import random_deg4, with_values
SAFE = os.environ.get('PLAIN') is None      # PLAIN=1: Algorithm 2 without the G1 repair
from sources import cores, domains


def attempt(I, rng, C, tries=3):
    some = False
    for z in range(I.n):
        for rep in range(tries):
            lab = labels(I, z) if rep == 0 else random_labels(I, z, rng)
            r, Z = (lss_dyn_safe if SAFE else lss_dyn)(I, lab)
            C['runs'] += 1
            if Z is not None:
                assert is_efx0(I, Z)
                C['completed'] += 1
                some = True
                break
        if some:
            break
    C['instances'] += 1
    C['instances completed'] += some
    if not some:
        print('NO RUN COMPLETES', I, flush=True)


def main():
    mode, seed, secs = sys.argv[1], int(sys.argv[2]), float(sys.argv[3])
    rng = random.Random(seed)
    C = collections.Counter()
    t0 = time.time()
    print('$ python3 k4/girth/dyn_more.py', *sys.argv[1:], flush=True)
    if mode.startswith('cores'):
        allc = cores(int(mode[5:]))
        while time.time() - t0 < secs:
            f, idx, sets, m = rng.choice(allc)
            D = domains(sets, m)
            ds = [rng.choice(d) for d in D]
            attempt(Inst([sorted(d) for d in ds], [[d[g] for g in sorted(d)] for d in ds], m), rng, C)
            if C['instances'] % 500 == 0:
                print(dict(C), flush=True)
    else:
        while time.time() - t0 < secs:
            n = rng.randint(3, 9)
            e = random_deg4(n, rng, tries=rng.randint(4, 30), private=rng.choice([0, 0.3]))
            if not e:
                continue
            I = with_values(n, e, rng, mode=rng.choice(['uniform', 'flat', 'geom']))
            if not two_cycles(I):
                continue
            attempt(I, rng, C)
            if C['instances'] % 500 == 0:
                print(dict(C), flush=True)
    print(mode, dict(C), flush=True)


if __name__ == '__main__':
    main()
