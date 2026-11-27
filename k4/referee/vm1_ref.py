#!/usr/bin/env python3
"""Referee replay of P34 (attempts/k4-vm-vm1-core.md on claude/k4-vm): Conjecture VM1 (k4/vm.md §7.3) fails on the
connected k = 4 core 4_pure idx 34 (n = 4, m = 7). Own code: V-M Phases I-II written from k4/vm.md §2 (every
resolution of the matchings), VM1's moves from §6 / §7.3, and an exhaustive search over F1 placements and envy-cycle
rotations; raw EFX0 from cert_ref.py. Nothing from k4/vm/ or attempts/ is run or imported; the instance is copied
from the note.

VM1: some V-M matching Y, at most one move (a pool upgrade: an agent holding one good y swaps it for S ⊆ pool ∩ R_i
with v_i(S) > v_i(y), EFX0 kept, y back to the pool; or an unrestricted two-agent exchange: i holding one good y takes
{z} ∪ S, z any good of j, S ⊆ pool, j takes X_j - z + y, both strictly gain, EFX0 kept), then placements of pool goods
(g to s only if nobody EFX0-envies X_s + g) with envy-cycle rotations, ending complete and EFX0.
The search is a superset of VM1's schedule: rotations of any envy cycle at any time, placements in any order, and
upgrades with any S (not only minimal), so "no completion" here implies VM1 fails. It is run from the V-M matchings
and, more strongly, from every one-good-per-agent matching.
"""
import itertools, json, sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, efx0, subsets
from oc1p_ref import core_check

SETS = [[0, 2, 4, 5], [0, 2, 4, 6], [1, 3, 5, 6], [1, 3, 5, 6]]
VALS = [[4, 3, 2, 8], [4, 3, 2, 8], [4, 2, 8, 5], [4, 2, 8, 5]]
M = 7

def mk():
    v = [[0] * M for _ in SETS]
    for i, (s, x) in enumerate(zip(SETS, VALS)):
        for g, y in zip(s, x):
            v[i][g] = y
    return v

def ranking(v, i):
    return sorted((g for g in range(M) if v[i][g] > 0), key=lambda g: (-v[i][g], g))

def vm_matchings(v):
    n = len(v); rk = [ranking(v, i) for i in range(n)]
    r = lambda i, k: rk[i][k - 1] if len(rk[i]) >= k else None
    vv = lambda i, g: v[i][g] if g is not None else 0
    A = [i for i in range(n) if vv(i, r(i, 1)) > vv(i, r(i, 2)) + vv(i, r(i, 3))]
    out = set()
    def step(Y, Nr, claims):
        # claims: agent -> good; each good to one claimant (maximum matching of a graph with one edge per agent)
        goods = sorted(set(claims.values()))
        opts = [[i for i in claims if claims[i] == g] for g in goods]
        for choice in itertools.product(*opts):
            Y2 = dict(Y); Nr2 = set(Nr)
            for g, i in zip(goods, choice):
                Y2[i] = g; Nr2.discard(i)
            yield Y2, Nr2
    def phase2(Y, Nr, k):
        if k > 4:
            out.add(tuple(Y.get(i) for i in range(n))); return
        taken = set(Y.values())
        claims = {i: r(i, k) for i in Nr if r(i, k) is not None and r(i, k) not in taken}
        for Y2, Nr2 in step(Y, Nr, claims):
            phase2(Y2, Nr2, k + 1)
    claims = {i: r(i, 1) for i in A}
    for Y, Nr in step({}, set(range(n)), claims):
        phase2(Y, Nr, 1)
    return sorted(out)

def envious(v, X, i, j):
    return val(v, i, X[j]) > val(v, i, X[i])

def efx0_partial(v, X):
    return efx0(v, X)

def one_moves(v, X, pool, minimal_only=False):
    n = len(X); out = []
    for i in range(n):
        if len(X[i]) != 1:
            continue
        (y,) = X[i]
        Ri = {g for g in pool if v[i][g] > 0}
        for S in subsets(Ri):
            if S and val(v, i, S) > v[i][y]:
                if minimal_only and any(val(v, i, S - {g}) > v[i][y] for g in S):
                    continue
                Z = [set(b) for b in X]; Z[i] = set(S)
                if efx0_partial(v, Z):
                    out.append((("upgrade", i, sorted(S)), Z, (pool - S) | {y}))
        for j in range(n):
            if j == i:
                continue
            for z in X[j]:
                for S in subsets(pool):
                    Z = [set(b) for b in X]; Z[i] = {z} | S; Z[j] = (X[j] - {z}) | {y}
                    if val(v, i, Z[i]) > val(v, i, X[i]) and val(v, j, Z[j]) > val(v, j, X[j]) and efx0_partial(v, Z):
                        out.append((("exchange", i, j, z, sorted(S)), Z, pool - S))
    return out

def completes(v, X, pool):
    """exhaustive search over placements (F1) and envy-cycle rotations."""
    n = len(X); seen = set()
    stack = [(tuple(frozenset(b) for b in X), frozenset(pool))]
    while stack:
        Xs, P = stack.pop()
        if (Xs, P) in seen:
            continue
        seen.add((Xs, P))
        Xl = [set(b) for b in Xs]
        if not P and efx0(v, Xl):
            return [sorted(b) for b in Xl], len(seen)
        for g in P:
            for s in range(n):
                Z = [set(b) for b in Xl]; Z[s] = Z[s] | {g}
                if not any(i != s and len(Z[s]) >= 2 and any(val(v, i, Z[s] - {h}) > val(v, i, Z[i]) for h in Z[s]) for i in range(n)):
                    stack.append((tuple(frozenset(b) for b in Z), P - {g}))
        for L in range(2, n + 1):
            for cyc in itertools.permutations(range(n), L):
                if cyc[0] != min(cyc):
                    continue
                if all(envious(v, Xl, cyc[t], cyc[(t + 1) % L]) for t in range(L)):
                    Z = [set(b) for b in Xl]
                    for t in range(L):
                        Z[cyc[t]] = set(Xl[cyc[(t + 1) % L]])
                    stack.append((tuple(frozenset(b) for b in Z), P))
    return None, len(seen)

def main():
    v = mk(); n = len(v)
    agents, conn, allrel = core_check(v)
    print(json.dumps(dict(instance="P34 (4_pure idx 34)", core_agents=agents, connected=conn, every_good_relevant=allrel)))
    Ys = vm_matchings(v)
    print(json.dumps(dict(vm_matchings=Ys)))
    starts = {"V-M": Ys,
              "every one-good matching": [Y for Y in itertools.permutations(range(M), n) if all(v[i][Y[i]] > 0 for i in range(n))]}
    for label, ys in starts.items():
        zero = one = 0; moves_seen = []
        for Y in ys:
            X = [{y} for y in Y]; pool = set(range(M)) - set(Y)
            if not efx0(v, X):
                continue
            r0, _ = completes(v, X, pool)
            zero += r0 is not None
            for mv, Z, P in one_moves(v, X, pool):
                if label == "V-M":
                    moves_seen.append((Y, mv))
                r1, _ = completes(v, Z, P)
                one += r1 is not None
        print(json.dumps(dict(starts=label, count=len(ys), completing_with_zero_moves=zero, completing_after_one_move=one,
                              legal_moves_from_VM=moves_seen if label == "V-M" else "n/a")))
    # the two-move completion of the note: agent 0 upgrades to {0,2,4}, agent 2 upgrades to the released 5, 1 to agent 3
    X = [{0, 2, 4}, {6}, {5}, {3, 1}]
    print(json.dumps(dict(two_move_completion=[sorted(b) for b in X], efx0=efx0(v, X),
                          gains_vs_VM_matching_5_6_1_3=[val(v, i, X[i]) > v[i][y] for i, y in enumerate((5, 6, 1, 3))])))
    # the same as one DE chain of length 1 plus a placement, from Y = (5, 6, 1, 3)
    Z = [{0, 2, 4}, {6}, {5}, {3}]
    r, k = completes(v, Z, {1})
    print(json.dumps(dict(after_DE_chain_0_takes_024_2_takes_5=[sorted(b) for b in Z], efx0_partial=efx0(v, Z), completion=r)))

if __name__ == "__main__":
    main()
