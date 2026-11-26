"""Replays the failed approaches of proof/k4-girth (attempts/k4-girth-*.md).  Plain Python, raw EFX0 checks.

    python3 attempts/k4_girth_attempts.py
"""
import itertools
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'k4', 'girth'))
from lss import Inst, lss, labels, classify, is_efx0, envied, flex, flex2, two_cycles, triangles  # noqa: E402
from brute import pareto_max, park_condition, park_slack, completable, check_PL, bundles_of  # noqa: E402

# 1. The faithful LSS algorithm (vertex 0 = agent 0, default labels, largest label / smallest good on choices):
#    the smallest failing configuration found for each girth use (k4/girth.md, section 1.4).
FAITHFUL = [
    ('G1 (A2L4)', [{0: 2, 3: 1}, {0: 2, 1: 1, 2: 1, 4: 2}, {1: 1, 2: 1, 3: 3, 4: 3}]),
    ('G5 (A3L2)', [{0: 2, 1: 2, 2: 1}, {0: 1, 1: 1, 2: 1, 3: 2}]),
    ('G5 (A3L2 makes the receiver envied)', [{0: 4, 1: 3}, {2: 1, 3: 4, 4: 3, 5: 3}, {0: 2, 1: 2, 2: 2, 3: 1}]),
    ('G6', [{0: 3, 1: 1}, {0: 2, 1: 2, 2: 1, 3: 1}]),
    ('G3', [{0: 4}, {0: 1, 1: 3, 2: 2}, {0: 2, 1: 3, 3: 1, 4: 2}]),
    ('G4', [{1: 1, 2: 2, 3: 1}, {0: 3, 2: 2}, {0: 2, 1: 2, 4: 1}]),
    ('G4 (k4/girth.md section 2)', [{0: 1, 1: 7}, {1: 1, 2: 8}, {0: 6, 2: 7, 3: 4, 4: 1}]),
]

# 2. "Every Pareto-maximal partial EFX0 orientation of a linear instance satisfies the hypothesis of Lemma PARK":
#    false; the smallest counterexample found is a graph (CFKS's second scenario).  It is completed by SLACK.
PM_NOPARK = [{0: 12, 3: 11}, {0: 16, 2: 15, 4: 15}, {1: 13, 3: 12, 4: 12}, {1: 11, 2: 10}]

# 3. The LSS architecture with 2-cycles: Algorithm 2 (every labeling) + any sink, with or without the G5 repair,
#    fails on the n = 2 k = 4 core with two equal agents of type (8, 5, 4, 2); PL fails on GM4-E.
TWIN = [{0: 2, 1: 4, 2: 5, 3: 8}, {0: 2, 1: 4, 2: 5, 3: 8}]
GM4E = [{0: 3, 2: 10, 4: 6, 6: 2}, {1: 3, 3: 4, 5: 8, 6: 2}, {2: 4, 3: 2, 6: 3}, {4: 2, 5: 4, 6: 3}]


def all_labels(I):
    for z in range(I.n):
        nb = I.neighbours(z)
        rest = [a for a in range(I.n) if a != z and a not in nb]
        for p in itertools.permutations(nb):
            for q in itertools.permutations(rest):
                yield labels(I, z, p, q)


def main():
    print('1. faithful LSS, vertex 0 = agent 0:')
    for name, ds in FAITHFUL:
        I = Inst.from_dicts(ds)
        r = lss(I, lab=labels(I, 0))
        print('   %-38s n=%d m=%d  %s  final %s  EFX0 %s  2-cycles %d triangles %d'
              % (name, I.n, I.m, classify(r), [sorted(b) for b in r.X], is_efx0(I, r.X),
                 len(two_cycles(I)), len(triangles(I))))
        assert not is_efx0(I, r.X)
    print('2. a Pareto-maximal orientation without PARK (linear, a graph):')
    I = Inst.from_dicts(PM_NOPARK)
    assert not two_cycles(I) and triangles(I)
    bad = [(v, a) for v, A in pareto_max(I) for a in A if not park_condition(I, a)[0]]
    for v, a in bad:
        Z = park_slack(I, a)
        print('   values %s state %s bundles %s; PARK+SLACK completion %s' % (v, a, [sorted(b) for b in bundles_of(I, a)],
                                                                         [sorted(b) for b in Z]))
        assert Z is not None and is_efx0(I, Z)
    assert len(bad) == 1
    print('3. 2-cycles:')
    I = Inst.from_dicts(TWIN)
    efx = []
    for owner in itertools.product(range(2), repeat=I.m):
        X = [{g for g in range(I.m) if owner[g] == i} for i in range(2)]
        if is_efx0(I, X):
            efx.append([sorted(b) for b in X])
    print('   twin core: EFX0 allocations', efx)
    worked = 0
    for lab in all_labels(I):
        worked += bool(flex(I, lab)[1]) + bool(flex2(I, lab)[1])
        worked += is_efx0(I, lss(I, lab=lab).X)
    print('   twin core: runs of Algorithm 2 + a sink (paper, flexible, flexible + G5 repair) that give EFX0:', worked)
    assert worked == 0
    I = Inst.from_dicts(GM4E)
    ok, cex = check_PL(I)
    print('   GM4-E (2-cycles): every Pareto-maximal orientation completable?', ok, cex)
    assert not ok


if __name__ == '__main__':
    main()
