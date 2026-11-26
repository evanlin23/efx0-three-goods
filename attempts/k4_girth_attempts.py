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
# 4. Conjecture L / PL for linear instances: a Pareto-maximal partial EFX0 orientation with no EFX0 completion.
#    goods: 0 e{i,j}, 1 x_i{i,r}, 2 x_j{j,s}, 3 f{r,j}, 4 h{s,i}, 5 g{r}, 6 g'{s}; agents i=0, j=1, r=2, s=3.
PL_CEX = [{1: 10, 0: 6, 4: 6}, {2: 10, 0: 6, 3: 6}, {1: 10, 3: 4, 5: 4}, {2: 10, 4: 4, 6: 4}]
PL_STATE = (-1, 0, 1, 2, 3, 2, 3)
# 4b. The same configuration inside a strict linear k = 4 core: n = 5, m = 11, every agent has 4 goods.
#    extra goods 7 t{r,w}, 8 t'{s,w}, 9 q_i{i,w}, 10 q_j{j,w}; extra agent w = 4.
PL_CORE = [{1: 20, 0: 12, 4: 13, 9: 9}, {2: 20, 0: 12, 3: 13, 10: 9}, {1: 20, 3: 7, 5: 6, 7: 8},
           {2: 20, 4: 7, 6: 6, 8: 8}, {9: 10, 10: 7, 7: 4, 8: 2}]
PL_CORE_STATE = (-1, 0, 1, 2, 3, 2, 3, 4, 4, 4, 4)
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
    print('4. Conjecture L / PL on a linear instance (n = 4, m = 7, three goods per agent):')
    I = Inst.from_dicts(PL_CEX)
    assert not two_cycles(I) and triangles(I)
    pm = pareto_max(I)
    assert any(PL_STATE in A for v, A in pm)
    assert completable(I, PL_STATE) is None
    print('   state %s (bundles %s) is Pareto-maximal and has no EFX0 completion'
          % (PL_STATE, [sorted(b) for b in bundles_of(I, PL_STATE)]))
    n_ok = sum(bool(flex(I, lab)[1]) for lab in all_labels(I))
    print('   LSS Algorithm 2 + flexible sink: EFX0 on %d of %d labelings' % (n_ok, len(list(all_labels(I)))))
    for ds, st, name in ((PL_CEX, PL_STATE, 'n=4 instance'), (PL_CORE, PL_CORE_STATE, 'n=5 linear k=4 core')):
        indep_check(ds, st, name)


def indep_check(ds, state, name):
    """Independent re-check (no code from k4/girth): the state is a partial EFX0 orientation, no partial EFX0
    orientation Pareto-dominates it, and no way of adding its unallocated goods to bundles is EFX0."""
    n, m = len(ds), 1 + max(g for d in ds for g in d)
    val = lambda i, B: sum(ds[i].get(g, 0) for g in B)

    def ok(B):                                   # raw EFX0 for a list of bundles (partial allowed)
        for i in range(n):
            mine = val(i, B[i])
            for k in range(n):
                if k != i:
                    for g in B[k]:
                        if mine < val(i, B[k]) - ds[i].get(g, 0):
                            return False
        return True

    def bundles(owner):
        B = [[] for _ in range(n)]
        for g, a in enumerate(owner):
            if a is not None:
                B[a].append(g)
        return B

    st = [None if a < 0 else a for a in state]
    B0 = bundles(st)
    assert ok(B0) and all(g in ds[a] for g, a in enumerate(st) if a is not None)
    base = [val(i, B0[i]) for i in range(n)]
    dominated = 0
    owner = [None] * m

    def rec(g):
        nonlocal dominated
        if g == m:
            B = bundles(owner)
            vec = [val(i, B[i]) for i in range(n)]
            if all(x >= y for x, y in zip(vec, base)) and vec != base and ok(B):
                dominated += 1
            return
        for a in [None] + [i for i in range(n) if g in ds[i]]:
            owner[g] = a
            rec(g + 1)
        owner[g] = None
    rec(0)
    U = [g for g, a in enumerate(st) if a is None]
    completions = 0
    for extra in itertools.product(range(n), repeat=len(U)):
        own = list(st)
        for g, a in zip(U, extra):
            own[g] = a
        completions += ok(bundles(own))
    print('   independent check (%s): dominating orientations %d, EFX0 completions %d' % (name, dominated, completions))
    assert dominated == 0 and completions == 0


if __name__ == '__main__':
    main()
