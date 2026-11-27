"""Pure reduction is not a complete base case (attempts/k4-matching-rsd-base.md).  Independent of k4/: it reuses only
the raw primitives of attempts/k4_matching_rsd_n5.py.

The coordinator's question: at a start with a one-move repair, do reduction steps alone repair it?  A step is a
canonical chain from a currently dangerous agent whose head takes an improving T inside junk + the end's good.  The
reduced start must be a perfect SD outcome, and the sequence ends in a completion at once.  Tested here, from the most
to the least restrictive form:
  (i)   (L*) at each step; the completion gives the junk to present agents only;
  (ii)  (L*) deferred to the final test;
  (iii) also deferred, and deleted agents may receive junk in the completion.
Every completion is a one-absorber completion over the allowed agents, the campaign's shape.  The script runs
form (iii) on the starts that k4/matching/rsd.py (DEADRECV=1 TSIZE=any LSTAR=defer) leaves unrepaired.  For each of
them it also shows a one-move repair (k4/sdc's official move set: a chain whose middle agents may take junk).

    python3 attempts/k4_matching_rsd_base.py"""
import json, itertools, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k4_matching_rsd_n5 import Inst, steps

STARTS = [  # the 6 starts of results/k4_matching/rsd_onemove_*.log that form (iii) leaves unrepaired (k4/matching.md §6)
    dict(name='Q2 / log555', sets=[[0, 1, 3, 4], [2, 3, 6, 7], [2, 5, 7], [4, 5, 6, 7]],
         vals=[[2, 3, 10, 6], [2, 8, 3, 4], [2, 4, 3], [4, 8, 2, 3]], picks=[3, 7, 5, 4]),
    dict(name='c4one-one-rotation-m8 / log792', sets=[[0, 2, 4, 7], [1, 2, 3], [1, 5, 6], [3, 5, 7], [4, 6, 7]],
         vals=[[2, 8, 3, 4], [3, 4, 2], [2, 4, 3], [2, 4, 3], [2, 4, 3]], picks=[7, 2, 1, 5, 6]),
    dict(name='ls-alt-rule-n4m7 / log794', sets=[[0, 1, 2, 3], [0, 2, 5, 6], [1, 4, 5, 6], [3, 4, 5, 6]],
         vals=[[3, 6, 10, 8], [2, 8, 4, 3], [4, 2, 5, 8], [4, 3, 2, 8]], picks=[2, 5, 6, 3]),
    dict(name='(multi n = 4)', sets=[[0, 3, 5, 7], [1, 4, 5, 6], [2, 4, 6, 7], [3, 6, 7]],
         vals=[[2, 8, 4, 7], [2, 8, 3, 4], [2, 10, 6, 7], [4, 3, 2]], picks=[3, 4, 7, 6]),
    dict(name='(multi n = 4, m = 9)', sets=[[0, 4, 5, 6], [1, 4, 6, 8], [2, 5, 7, 8], [3, 7, 8]],
         vals=[[3, 4, 10, 8], [3, 2, 4, 8], [1, 8, 6, 4], [2, 3, 4]], picks=[5, 6, 7, 8]),
    dict(name='(multi n = 5)', sets=[[0, 3, 7], [1, 5, 8], [2, 6, 7, 8], [3, 4, 5], [4, 6, 8]],
         vals=[[2, 3, 4], [2, 4, 3], [2, 3, 8, 4], [2, 3, 4], [4, 2, 3]], picks=[7, 5, 8, 3, 4]),
]


def completes(I, B, recv):
    """A one-absorber completion over the allowed agents: one owner takes any junk, every other allowed agent at most
    one good (the campaign's completion shape)."""
    J = [g for g in range(I.m) if all(g not in b for b in B)]
    for o in recv:
        others = [u for u in recv if u != o]
        for lab in itertools.product([o] + others, repeat=len(J)):
            if any(lab.count(u) > 1 for u in others): continue
            X = [list(b) for b in B]
            for g, a in zip(J, lab): X[a].append(g)
            if I.efx0(X): return X
    return None


def rsd(I, B, alive, goods, lstar, deadrecv, depth):
    if completes(I, B, list(range(I.n)) if deadrecv else alive) is not None: return True
    if depth == 0: return False
    return any(rsd(I, nb, al2, g2, lstar, deadrecv, depth - 1)
               for k, T, P, nb, al2, g2 in steps(I, B, alive, goods, lstar))


def one_move(I, B):
    """A one-move repair: a chain (x0..xt), each x_i (i >= 1) taking x_{i-1}'s bundle plus a set of junk and gaining,
    x0 taking junk + goods of x_t's bundle, then a one-absorber completion of the rest."""
    n = I.n; J = [g for g in range(I.m) if all(g not in b for b in B)]
    for L in range(2, n + 1):
        for P in itertools.permutations(range(n), L):
            pool = J + list(B[P[-1]])
            for r in range(1, len(pool) + 1):
                for H0 in itertools.combinations(pool, r):
                    if I.V(P[0], H0) <= I.V(P[0], B[P[0]]): continue
                    rest = [g for g in J if g not in H0]
                    for lab in itertools.product(range(L), repeat=len(rest)):
                        nb = [list(b) for b in B]; nb[P[0]] = list(H0)
                        for i in range(1, L): nb[P[i]] = list(B[P[i - 1]]) + [g for g, l in zip(rest, lab) if l == i]
                        if all(I.V(P[i], nb[P[i]]) > I.V(P[i], B[P[i]]) for i in range(1, L)):
                            X = completes(I, nb, list(range(n)))
                            if X is not None: return P, list(H0), nb, X
    return None


if __name__ == '__main__':
    print('$ python3 attempts/k4_matching_rsd_base.py')
    for c in STARTS:
        I = Inst(c['sets'], c['vals']); n = I.n; B = [[g] for g in c['picks']]; allg = set(range(I.m))
        assert any([I.sd(o, allg).get(i) for i in range(n)] == c['picks'] for o in itertools.permutations(range(n)))
        assert completes(I, B, list(range(n))) is None
        forms = [rsd(I, B, list(range(n)), allg, ls, dr, n) for ls, dr in ((True, False), (False, False), (False, True))]
        mv = one_move(I, B)
        print('==', c['name'], '| n', n, 'm', I.m, '| pure reduction, forms (i) (ii) (iii):', forms)
        print('   a one-move repair: chain', mv[0], 'head takes', mv[1], '->', mv[2], '; completion', mv[3])
        mids = [i for i in mv[0][1:] if len(mv[2][i]) > 1]
        print('   chain agents after the head that take junk:', mids)
        assert not any(forms) and mv is not None
    print('pure reduction is not a complete base case: these 6 one-move starts need a move it cannot express')
