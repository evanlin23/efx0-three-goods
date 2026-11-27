"""The smallest counterexample to Conjecture CAN2 (k4/p3.md section 6; attempts/k4-p3-can2.md), checked by plain
enumeration only (no SAT): a multigraph core (every good valued by at most two agents) with n = 4, m = 7 and maximum-
matching serial-dictatorship picks that have no one-absorber EFX0 completion, where no canonical chain repairs but
a chain of four agents in which a middle agent adds junk does. Also lists every official move (k4/p3/oc1max.py's
generator) and which ones repair, by enumeration, so "only chains of four repair" and "no ED chain repairs" are
checked without SAT.
    python3 k4/p3/can2_smallest.py
"""
import sys, os, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
from p3lib import Inst, sd, efx0

SETS = [[0, 1, 2, 3], [0, 2, 5], [1, 4, 5, 6], [3, 4, 6]]
VALS = [[4, 2, 3, 8], [3, 2, 4], [2, 3, 8, 4], [4, 2, 3]]


def complete(I, base):
    held = set().union(*base); J = [g for g in range(I.m) if g not in held]
    for own in itertools.product(range(I.n), repeat=len(J)):
        c = collections.Counter(own)
        if sum(1 for a in c if c[a] >= 2) > 1: continue
        X = [sorted(set(b) | {g for g, a in zip(J, own) if a == i}) for i, b in enumerate(base)]
        if efx0(I, X): return X
    return None


if __name__ == '__main__':
    I = Inst(SETS, VALS)
    import check4                                                     # k4/check4.py: the official core test
    print('core:', check4.is_core(I.n, I.m, SETS, False)[0], ' goods with at most two valuers:', I.p() <= 2)
    Y = sd(I, (1, 2, 3, 0)); print('picks of the order (1, 2, 3, 0):', Y)
    base = tuple(frozenset([y]) for y in Y)
    J = [g for g in range(I.m) if g not in Y]; p = [I.v[i][Y[i]] for i in range(I.n)]
    wants = {(i, j) for i in range(I.n) for j in range(I.n) if i != j and I.v[i].get(Y[j], 0) > p[i]}
    print('junk', J, '; i wants Y_j:', sorted(wants))
    print('one-absorber completion at the picks:', complete(I, base))
    # canonical chains: from a frozen k along the unique wanters to an unfrozen head z; k takes H0 in (J + {Y_z}) & R_k
    w = {j: [i for i in range(I.n) if (i, j) in wants] for j in range(I.n)}
    for k in range(I.n):
        if not w[k]: continue
        P = [k]
        while w[P[-1]]: P.append(w[P[-1]][0])
        z = P[-1]; pool = [g for g in J + [Y[z]] if g in I.R[k]]
        imp = [H for r in range(1, len(pool) + 1) for H in itertools.combinations(pool, r) if I.val(k, H) > p[k]]
        print(f'canonical chain P({k}) = {P}: pool {pool}, improving sets {imp}')
        for H in imp:
            B = list(base); B[k] = frozenset(H)
            for i in range(1, len(P)): B[P[i]] = frozenset([Y[P[i - 1]]])
            print('   completion after it:', complete(I, B))
    from oc1max import Checker
    K = Checker(I); rep = collections.Counter(); ok = []
    for st, tag in K.moves(base).items():
        X = complete(I, st)
        if X is not None: rep[(tag[2], tag[1])] += 1; ok.append(([sorted(b) for b in st], X))
    K.close()
    print('repairing official moves (by enumeration):', dict(rep))
    for st, X in ok: print('   bases', st, '-> EFX0 allocation', X)
