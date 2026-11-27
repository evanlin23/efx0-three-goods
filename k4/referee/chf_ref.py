#!/usr/bin/env python3
"""Referee check of Proposition CH-F (kgen/charity.md §6, branch claude/kgen-charity) for the k = 4 instance
(S'(3, 4)'s hypergraph, n = 9, m = 14, values from attempts/kgen-charity-welfare-maxima.md, read as data).
Shares no code with kgen/charity/; uses neither SAT nor MILP.

Claim: the stated state (goods 6, 7 out, total 198) is EFX0, and every partial EFX0 allocation leaving at most one
good out has total <= 197.

Method. If X is EFX0, then X^v (keep only the goods held by one of their valuers) is EFX0 with the same welfare:
removing a good its holder does not value changes no agent's own value and only shrinks bundles. So:
 (1) enumerate every EFX0 *orientation* (each good to one of its valuers, or set aside) with welfare >= TARGET,
     by depth-first search with a welfare bound and a sound envy bound (i's value can still grow by at most the
     best goods it may yet receive);
 (2) for each, search all placements of the set-aside goods on non-valuers (at most one left out) for an EFX0
     allocation. The claim holds iff no orientation of step (1) admits such a placement.
"""
import itertools, sys, json

ROWS = [  # (agent, {good: value}, holds)
    ("c(g0,j0)", {0: 20, 6: 21, 8: 40}, {8}),
    ("c(g1,j0)", {0: 12, 7: 16, 9: 27}, {9}),
    ("c(g0,j1)", {2: 20, 6: 21, 10: 40}, {10}),
    ("c(g1,j1)", {2: 12, 7: 13, 11: 24}, {11}),
    ("c(g0,j2)", {4: 20, 6: 21, 12: 40}, {12}),
    ("c(g1,j2)", {4: 9, 7: 10, 13: 18}, {13}),
    ("s0", {0: 2, 1: 1, 12: 7, 13: 4}, {0, 1}),
    ("s1", {2: 2, 3: 1, 8: 5, 9: 4}, {2, 3}),
    ("s2", {4: 2, 5: 1, 10: 8, 11: 4}, {4, 5}),
]
ROWS3 = [  # k = 3 instance (S'(3, 3) with relays, n = 12, m = 17); values from kgen/charity/w_counterexample.py (data)
    ("c(g0,j0)", {0: 18, 6: 20, 8: 37}, {8}), ("c(g1,j0)", {0: 28, 7: 33, 9: 60}, {9}),
    ("c(g0,j1)", {2: 15, 6: 16, 10: 30}, {10}), ("c(g1,j1)", {2: 30, 7: 31, 11: 60}, {11}),
    ("c(g0,j2)", {4: 25, 6: 24, 12: 48}, {12}), ("c(g1,j2)", {4: 32, 7: 29, 13: 60}, {13}),
    ("relay2", {12: 59, 13: 60, 14: 58}, {14}), ("s0", {0: 2, 1: 1, 14: 4}, {0, 1}),
    ("relay0", {8: 59, 9: 60, 15: 58}, {15}), ("s1", {2: 2, 3: 1, 15: 4}, {2, 3}),
    ("relay1", {10: 59, 11: 60, 16: 58}, {16}), ("s2", {4: 8, 5: 1, 16: 10}, {4, 5}),
]
WHICH = sys.argv[1] if len(sys.argv) > 1 else "k4"
if WHICH == "k3":
    ROWS = ROWS3
N = len(ROWS); M = 1 + max(g for r in ROWS for g in r[1])
V = [[ROWS[i][1].get(g, 0) for g in range(M)] for i in range(N)]
TOTAL = sum(sum(r[1][g] for g in r[2]) for r in ROWS)

def val(i, S):
    return sum(V[i][g] for g in S)

def efx0(X):
    for i in range(N):
        t = val(i, X[i])
        for j in range(N):
            if i != j and len(X[j]) >= 2:
                tot = val(i, X[j])
                for h in X[j]:
                    if tot - V[i][h] > t:
                        return False
    return True

def stranded_state():
    X = [set(r[2]) for r in ROWS]
    out = set(range(M)) - set().union(*X)
    return X, out

def enumerate_orientations(target):
    valuers = [[i for i in range(N) if V[i][g] > 0] for g in range(M)]
    order = sorted(range(M), key=lambda g: -max(V[i][g] for i in valuers[g]))
    best_of = [max(V[i][g] for i in valuers[g]) for g in range(M)]
    suffix = [0] * (M + 1)
    for k in range(M - 1, -1, -1):
        suffix[k] = suffix[k + 1] + best_of[order[k]]
    # potential gain of agent i from goods order[k:]
    gain = [[0] * (M + 1) for _ in range(N)]
    for i in range(N):
        for k in range(M - 1, -1, -1):
            gain[i][k] = gain[i][k + 1] + V[i][order[k]]
    X = [set() for _ in range(N)]; vals = [0] * N
    found = []
    def ok_partial(k):
        # sound prune: a strong-envy violation i -> j that persists even if i receives all goods it values among
        # order[k:] (j's bundle can only grow, which only strengthens the threat)
        for i in range(N):
            cap = vals[i] + gain[i][k]
            for j in range(N):
                if i != j and len(X[j]) >= 2:
                    tot = val(i, X[j])
                    for h in X[j]:
                        if tot - V[i][h] > cap:
                            return False
        return True
    def rec(k, W):
        if W + suffix[k] < target:
            return
        if not ok_partial(k):
            return
        if k == M:
            if efx0(X):
                aside = [g for g in range(M) if not any(g in x for x in X)]
                found.append(([set(x) for x in X], aside, W))
            return
        g = order[k]
        for i in valuers[g]:
            X[i].add(g); vals[i] += V[i][g]
            rec(k + 1, W + V[i][g])
            X[i].discard(g); vals[i] -= V[i][g]
        rec(k + 1, W)  # set aside
    rec(0, 0)
    return found

def placeable(X, aside, max_out=1):
    """can the set-aside goods be placed on non-valuers (at most max_out left out) keeping EFX0?"""
    aside = list(aside)
    def rec(idx, outs):
        if idx == len(aside):
            return efx0(X)
        g = aside[idx]
        for j in range(N):
            if V[j][g] == 0:
                X[j].add(g)
                # prune: placing g on j can only strengthen threats toward j; check j's bundle now
                okj = True
                for i in range(N):
                    if i != j and len(X[j]) >= 2:
                        t = val(i, X[i]); tot = val(i, X[j])
                        if any(tot - V[i][h] > t for h in X[j]):
                            okj = False; break
                if okj and rec(idx + 1, outs):
                    X[j].discard(g); return True
                X[j].discard(g)
        if outs < max_out and rec(idx + 1, outs + 1):
            return True
        return False
    return rec(0, 0)

if __name__ == "__main__":
    X, out = stranded_state()
    W = sum(val(i, X[i]) for i in range(N))
    print(json.dumps(dict(stranded_state_efx0=efx0(X), unallocated=sorted(out), total=W)))
    print(json.dumps(dict(instance=WHICH, n=N, m=M, k=max(len(r[1]) for r in ROWS))))
    for target in (TOTAL,):
        found = enumerate_orientations(target)
        print(json.dumps(dict(target=target, efx0_orientations_with_welfare_at_least_target=len(found),
                              welfare_values=sorted({w for _, _, w in found}))))
        n_place = 0; witnesses = []
        for Xv, aside, w in found:
            if placeable([set(x) for x in Xv], aside):
                n_place += 1
                witnesses.append((w, [sorted(x) for x in Xv], aside))
        print(json.dumps(dict(orientations_completable_with_at_most_one_out=n_place, examples=witnesses[:3])))
    # sanity: the method must find completable states at a lower target (the claim says the best is 197)
    found = enumerate_orientations(TOTAL - 1)
    best = None
    for Xv, aside, w in sorted(found, key=lambda t: -t[2]):
        if placeable([set(x) for x in Xv], aside):
            best = (w, [sorted(x) for x in Xv], aside); break
    print(json.dumps(dict(sanity_target=TOTAL - 1, orientations=len(found), best_completable_with_at_most_one_out=best)))
