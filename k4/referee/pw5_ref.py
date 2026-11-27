#!/usr/bin/env python3
"""Referee check of PW5 (k4/ksens.md §1, branch claude/k4-ksens): OC and OC1 fail at k = 5.
Written from the table in ksens.md; shares no code with k4/ksens/ or k4/sdc/.

1. Enumerate all 5^9 complete allocations, keep the EFX0 ones (raw definition).
2. For every order of the 5 agents: SD picks; every improving chain of k4/sdc.md §29 (t >= 1; H0 ⊆ J ∪ B_{x_t},
   H_i ⊆ J, all inside the receivers' relevant goods, strict gains), and also the t = 0 moves (one agent replaces its
   base by H0 ⊆ J ∪ B_{x0} worth more). A state *extends* if some EFX0 allocation contains every base (free
   completion). Report, per order, whether the picks extend, how many chain states there are, how many extend.
"""
import itertools, json, sys

N = 5; M = 9
v = [[0] * M for _ in range(N)]
for j in range(3):
    v[j][j] = 10
    for g, x in zip((5, 6, 7, 8), (9, 8, 7, 6)):
        v[j][g] = x
for w, q in ((3, 3), (4, 4)):
    v[w][0], v[w][1], v[w][2], v[w][q] = 6, 4, 2, 1

def val(i, S):
    return sum(v[i][g] for g in S)

def efx0(X):
    for i in range(N):
        t = val(i, X[i])
        for j in range(N):
            if i != j and len(X[j]) >= 2:
                tot = val(i, X[j])
                if any(tot - v[i][h] > t for h in X[j]):
                    return False
    return True

def all_efx0():
    out = []
    for f in itertools.product(range(N), repeat=M):
        X = [set() for _ in range(N)]
        for g, a in enumerate(f):
            X[a].add(g)
        if efx0(X):
            out.append(f)
    return out

def sd(order):
    G = set(range(M)); Y = {}
    for i in order:
        R = sorted((g for g in G if v[i][g] > 0), key=lambda g: (-v[i][g], g))
        Y[i] = {R[0]} if R else set()
        if R:
            G -= {R[0]}
    return [Y[i] for i in range(N)]

def subsets(S):
    S = sorted(S)
    for k in range(len(S) + 1):
        for c in itertools.combinations(S, k):
            yield set(c)

def rel(i):
    return {g for g in range(M) if v[i][g] > 0}

def chains(B, with_t0=True):
    J = set(range(M)) - set().union(*B)
    out = []
    for t in range(0 if with_t0 else 1, N):
        for seq in itertools.permutations(range(N), t + 1):
            def rec(i, used, nb):
                if i > t:
                    pool = ((J - used) | B[seq[-1]]) & rel(seq[0])
                    for H0 in subsets(pool):
                        if H0 and val(seq[0], H0) > val(seq[0], B[seq[0]]) and H0 != B[seq[0]]:
                            c = list(nb); c[seq[0]] = set(H0); out.append((t, c))
                    return
                xi, pr = seq[i], seq[i - 1]
                for Hi in subsets((J - used) & rel(xi)):
                    if val(xi, B[pr] | Hi) > val(xi, B[xi]):
                        c = list(nb); c[xi] = B[pr] | Hi
                        rec(i + 1, used | Hi, c)
            rec(1, set(), [set(b) for b in B])
    return out

def extends(B, sols):
    for f in sols:
        if all(f[g] == i for i in range(N) for g in B[i]):
            return True
    return False

if __name__ == "__main__":
    sols = all_efx0()
    print(json.dumps(dict(instance="PW5", k=max(len(rel(i)) for i in range(N)), efx0_allocations=len(sols))))
    seen = {}
    for order in itertools.permutations(range(N)):
        B = sd(order)
        key = tuple(tuple(sorted(b)) for b in B)
        if key in seen:
            continue
        ext = extends(B, sols)
        if ext:
            seen[key] = dict(order=order, picks=[sorted(b) for b in B], picks_extend=True)
            continue
        cs = chains(B)
        n1 = sum(1 for t, c in cs if t >= 1); n0 = len(cs) - n1
        good1 = sum(1 for t, c in cs if t >= 1 and extends(c, sols))
        good0 = sum(1 for t, c in cs if t == 0 and extends(c, sols))
        seen[key] = dict(order=order, picks=[sorted(b) for b in B], picks_extend=False, chain_states_t_ge_1=n1,
                         extending_t_ge_1=good1, moves_t0=n0, extending_t0=good0)
    for k_, d in seen.items():
        print(json.dumps(d))
    bad = [d for d in seen.values() if not d["picks_extend"] and d["extending_t_ge_1"] == 0]
    print(json.dumps(dict(distinct_starts=len(seen), starts_where_OC_fails=len(bad),
                          failing_orders=[d["order"] for d in bad])))
