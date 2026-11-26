"""Brute force over partial orientations (k4/girth.md, section 4).  Written from the raw definitions; shares only the
Inst class with lss.py.

A partial orientation gives each good to one of its valuers or leaves it unallocated (goods nobody values stay
unallocated).  It is EFX0 if no agent strongly envies another bundle (raw definition, all goods counted).

    pareto_max(I)          the Pareto-maximal value vectors among partial EFX0 orientations, with their orientations
    completable(I, X)      can the unallocated goods be added to bundles so that the complete allocation is EFX0?
    check_PL(I)            Conjecture PL: every Pareto-maximal partial EFX0 orientation is completable
"""
import itertools

from lss import Inst, is_efx0


def orientations(I):
    choices = [[-1] + sorted(I.edge[g]) for g in range(I.m)]
    for assign in itertools.product(*choices):
        X = [set() for _ in range(I.n)]
        for g, a in enumerate(assign):
            if a >= 0:
                X[a].add(g)
        yield assign, X


def efx0_partial(I, X):
    for i in range(I.n):
        vi = I.val(i, X[i])
        for j in range(I.n):
            if j != i and X[j] and vi < I.threat(i, X[j]):
                return False
    return True


def pareto_max(I):
    best = {}                                     # value vector -> list of assignments
    for assign, X in orientations(I):
        if not efx0_partial(I, X):
            continue
        vec = tuple(I.val(i, X[i]) for i in range(I.n))
        best.setdefault(vec, []).append(assign)
    vecs = list(best)
    out = []
    for v in vecs:
        if any(w != v and all(a >= b for a, b in zip(w, v)) for w in vecs):
            continue
        out.append((v, best[v]))
    return out


def completable(I, assign):
    U = [g for g, a in enumerate(assign) if a < 0]
    base = [set() for _ in range(I.n)]
    for g, a in enumerate(assign):
        if a >= 0:
            base[a].add(g)
    for extra in itertools.product(range(I.n), repeat=len(U)):
        X = [set(b) for b in base]
        for g, a in zip(U, extra):
            X[a].add(g)
        if is_efx0(I, X):
            return X
    return None


def check_PL(I, every=True):
    """every=True: every Pareto-max orientation completable; returns (ok, counterexample assign or None)"""
    pm = pareto_max(I)
    for vec, assigns in pm:
        for a in assigns:
            if completable(I, a) is None:
                return False, (vec, a)
    return True, None
