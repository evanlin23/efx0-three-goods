"""Replay for attempts/k4-girth-uniform-labeling.md: on the n = 3, m = 6 core below, no single labeling completes DYN's
pipeline (lss.py: Algorithm 2 with the G1 repair, then dynamic parking with envy-cycle rotation) on both profiles P1 and
P2, while each profile is completed by some labeling.  Uses lss.py only (numeric values), not dyncert.py.

    python3 attempts/k4_girth_uniform.py
"""
import itertools
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'k4', 'girth'))
from lss import Inst, Run, is_efx0, park_dynamic_ec, labels  # noqa: E402

SETS = [[0, 1, 2, 3], [0, 1, 4, 5], [2, 3, 4, 5]]          # results/k4_certs_3.json.gz, m = 6, core 17
P1 = [{0: 2, 1: 3, 2: 4, 3: 8}, {0: 4, 1: 6, 4: 1, 5: 8}, {2: 2, 3: 8, 4: 7, 5: 4}]
P2 = [{0: 3, 1: 5, 2: 6, 3: 7}, {0: 1, 1: 8, 4: 4, 5: 6}, {2: 4, 3: 8, 4: 2, 5: 3}]


def balanced_strict(d):
    vals = list(d.values())
    sums = {}
    for k in range(1, len(vals) + 1):
        for A in itertools.combinations(range(len(vals)), k):
            sums[A] = sum(vals[a] for a in A)
    for A in sums:
        for B in sums:
            if not set(A) & set(B):
                assert sums[A] != sums[B], 'not strict'
    assert 2 * max(vals) < sum(vals), 'not strictly balanced'


def completes(P, lab):
    I = Inst.from_dicts(P, 6)
    r = Run(I, lab, check=False)
    r.alg2_safe()
    if not is_efx0(I, r.X):
        return None
    Z = park_dynamic_ec(I, r.X, r.U)
    if Z is not None:
        assert is_efx0(I, Z) and sorted(g for b in Z for g in b) == list(range(6))
    return Z


def main():
    for P in (P1, P2):
        assert [sorted(d) for d in P] == SETS
        for d in P:
            balanced_strict(d)
    I = Inst.from_dicts(P1, 6)
    labs = [labels(I, z, p, q) for z in range(3) for p in itertools.permutations(I.neighbours(z))
            for q in itertools.permutations([a for a in range(3) if a != z and a not in I.neighbours(z)])]
    some = {1: False, 2: False}
    for lab in labs:
        a, b = completes(P1, lab), completes(P2, lab)
        some[1] |= a is not None
        some[2] |= b is not None
        print('labels', lab, '(vertex 0 = agent %d)' % lab.index(0), 'P1:', 'completes' if a else 'FAILS',
              '| P2:', 'completes' if b else 'FAILS')
        assert a is None or b is None, 'this labeling works on both'
    assert some[1] and some[2]
    print('no labeling completes both P1 and P2; each is completed by some labeling (DYN-exists holds on both)')


if __name__ == '__main__':
    main()
