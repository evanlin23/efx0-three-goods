"""Reproduces the two failed collector schemes for beta = 2 (attempts/beta2-pc-scheme.md, attempts/beta2-gpc-scheme.md).
A scheme is a finite family of allocations per core; for each connected core with m = 2n - 1 we enumerate the family,
compute raw EFX0 safety masks (frontier.raw_masks) and count the ranking profiles no allocation covers (frontier.certify).
  pc   the collector w is an agent with a private good; every agent without a private good holds two shared goods;
       every other agent with a private good holds one shared good, alone (then it is in J and w takes its private
       good) or with its private good.
  gpc  as pc, but the collector ("deficient agent") may be any agent; it holds one shared good fewer than its quota
       (quota: 1 for agents with a private good, 2 for the others) and collects its own private good and those of J.
Usage (from the repository root): python attempts/beta2_schemes.py pc|gpc n [n ...]"""
import sys, os, itertools, collections
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'src'))
from frontier import raw_masks, PERMS
from cores_nauty import gen_cores_nauty


def scheme(n, m, sets, collector_any):
    deg = collections.Counter(g for S in sets for g in S)
    priv = [next((g for g in S if deg[g] == 1), None) for S in sets]
    shared = [g for g in range(m) if deg[g] >= 2]
    out = set()
    for d in range(n):
        if priv[d] is None and not collector_any: continue
        choices = []
        for i, S in enumerate(sets):
            sh = [g for g in S if g != priv[i]]
            q = (1 if priv[i] is not None else 2) - (1 if i == d else 0)
            choices.append(list(itertools.combinations(sh, q)))
        for c in itertools.product(*choices):
            used = [g for t in c for g in t]
            if len(used) != len(set(used)) or len(used) != len(shared): continue
            cand = [i for i in range(n) if i != d and priv[i] is not None]
            for r in range(len(cand) + 1):
                for J in itertools.combinations(cand, r):
                    X = [None] * m
                    for i, t in enumerate(c):
                        for g in t: X[g] = i
                    for i in range(n):
                        if priv[i] is not None: X[priv[i]] = d if (i in J or i == d) else i
                    out.add(tuple(X))
    return [list(X) for X in out]


def uncovered(n, m, sets, allocs):
    cov = np.zeros((6,) * n, dtype=bool)
    for X in allocs:
        M = raw_masks(n, m, sets, X)
        cov[np.ix_(*(np.flatnonzero(M[i]) for i in range(n)))] = True
    return [tuple(int(k) for k in p) for p in zip(*np.nonzero(~cov))]


if __name__ == '__main__':
    mode, levels = sys.argv[1], [int(a) for a in sys.argv[2:]]
    for n in levels:
        m = 2 * n - 1; bad = 0
        for pi, sets in gen_cores_nauty(n, m):
            U = uncovered(n, m, sets, scheme(n, m, sets, collector_any=(mode == 'gpc')))
            if U:
                bad += 1
                ex = [tuple(sets[i][k] for k in PERMS[U[0][i]]) for i in range(n)]
                print(f"n={n} core {sets}: {len(U)} of {6 ** n} profiles uncovered; e.g. (a, b, c) per agent: {ex}")
        print(f"{mode}: n={n}: {bad} of {len(gen_cores_nauty(n, m))} cores have an uncovered profile")
