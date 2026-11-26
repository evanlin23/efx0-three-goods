"""Conjecture DYN-EC (k4/girth.md section 5): for EVERY labeling, LSS's Algorithm 2 with the G1 repair, followed by
dynamic parking with envy-cycle rotation (lss.park_dynamic_ec), completes.  EVIDENCE only.

    python3 k4/girth/dynec_all.py sets               screen, suite, the k = 5 and OC/OC1 counterexamples (dyn_ksens.py)
    python3 k4/girth/dynec_all.py cores N SEED SECS  random strict profiles of random cores with n = N, every labeling
    python3 k4/girth/dynec_all.py random SEED SECS   random degree-<=4 instances with 2-cycles (n <= 8), every labeling
Prints every failing run.  Labelings: all of them for n <= 6 (capped at 720), else every vertex 0 with 3 random orders.
"""
import collections
import itertools
import random
import sys
import time

from lss import Inst, labels, random_labels, Run, is_efx0, park_dynamic, park_dynamic_ec, two_cycles
from gen import random_deg4, with_values


def labelings(I, rng, cap=720):
    out = []
    for z in range(I.n):
        nb = I.neighbours(z)
        rest = [a for a in range(I.n) if a != z and a not in nb]
        for p in itertools.permutations(nb):
            for q in itertools.permutations(rest):
                out.append(labels(I, z, p, q))
                if len(out) > cap:
                    return [labels(I, z2) for z2 in range(I.n)] + [random_labels(I, z2, rng) for z2 in range(I.n)
                                                                    for _ in range(3)]
    return out


def run_one(I, lab, C, name=''):
    r = Run(I, lab)
    r.alg2_safe()
    C['runs'] += 1
    if not is_efx0(I, r.X):
        C['Algorithm 2 broke EFX0'] += 1
        print('ALG2 BROKE', name, I, lab, flush=True)
        return False
    if park_dynamic(I, r.X, r.U) is not None:
        C['dynamic parking alone'] += 1
        return True
    Z = park_dynamic_ec(I, r.X, r.U)
    if Z is None:
        C['FAIL'] += 1
        print('FAIL', name, I, 'labels', lab, 'state', [sorted(b) for b in r.X], 'U', sorted(r.U), flush=True)
        return False
    assert is_efx0(I, Z) and sorted(g for b in Z for g in b) == list(range(I.m))
    C['needed an envy-cycle rotation'] += 1
    return True


def main():
    mode = sys.argv[1]
    print('$ python3 k4/girth/dynec_all.py', *sys.argv[1:], flush=True)
    C = collections.Counter()
    if mode == 'sets':
        from sources import screen, suite
        from dyn_ksens import INSTANCES
        rng = random.Random(1)
        groups = [('screen', [(n, I) for n, I in screen()]), ('suite', [(n, I) for n, I in suite()]),
                  ('k=5 and OC counterexamples', INSTANCES)]
        for gname, insts in groups:
            G = collections.Counter()
            for name, I in insts:
                G['instances'] += 1
                ok = all([run_one(I, lab, G, name) for lab in labelings(I, rng)])
                G['instances: every labeling completes'] += ok
            print(gname, dict(G), flush=True)
            C.update(G)
    else:
        seed, secs = int(sys.argv[-2]), float(sys.argv[-1])
        rng = random.Random(seed)
        t0 = time.time()
        if mode == 'cores':
            from sources import cores, domains
            allc = cores(int(sys.argv[2]))
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
            C['instances'] += 1
            ok = all([run_one(I, lab, C) for lab in labelings(I, rng)])
            C['instances: every labeling completes'] += ok
            if C['instances'] % 1000 == 0:
                print(dict(C), flush=True)
    print('total', dict(C), flush=True)


if __name__ == '__main__':
    main()
