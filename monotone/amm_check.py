"""Check the three-agent, eight-good counterexample of Akrami, Mackenzie, Mayorov, Mehlhorn,
Srinivas, Suzuki, Weidenbach, "EFX Need Not Exist", arXiv 2604.18216v4, Section 3.1.1
(read 2026-11-26), from the raw definitions, and record each agent's relevance.

Goods: A1 A2 B1 B2 C1 C2 x y (indices 0..7); agents a, b, c with types A, B, C.
For agent i with type T and other types U, V (eq. (2) of the paper):
    pair:   Ty  UV  Tx  Uy,Vy  TU,TV  TT,UU,VV,Ux,Vx,xy
    u_i:     6   5   4     3      2           1
u_i(empty) = 0, u_i({g}) = 1, and for larger bundles u_i = value of the best pair.
v_i(S) = 7 if S contains a triple of type UVx, else u_i(S)   (eq. (3)).

Prints: monotonicity, relevant goods per agent (k_i), number of EFX0 allocations of u
(the paper's Proposition 3.2 says exactly the 3! relabellings... of (Ay, BCCx, AB), counted
with the choice of A-good etc.) and of v (Theorem 3.4: none).
Also tests the obvious modifications: deleting any good, merging any two goods.

Usage: python3 monotone/amm_check.py
"""
import sys
import os
from itertools import combinations

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mono_lib import (check_normalized_monotone, relevant_goods, all_efx0, popcount)

NAMES = ["A1", "A2", "B1", "B2", "C1", "C2", "x", "y"]
TYPE = {0: "A", 1: "A", 2: "B", 3: "B", 4: "C", 5: "C", 6: "x", 7: "y"}
AGENT_TYPE = ["A", "B", "C"]


def pair_value(t, s1, s2):
    """Value of a two-good bundle with types s1, s2 for the agent of type t."""
    others = [z for z in "ABC" if z != t]
    U, V = others
    key = frozenset([s1, s2]) if s1 != s2 else None
    if s1 == s2:
        return 1  # TT, UU, VV (and xx, yy cannot occur)
    if key == frozenset([t, "y"]):
        return 6
    if key == frozenset([U, V]):
        return 5
    if key == frozenset([t, "x"]):
        return 4
    if key in (frozenset([U, "y"]), frozenset([V, "y"])):
        return 3
    if key in (frozenset([t, U]), frozenset([t, V])):
        return 2
    return 1  # Ux, Vx, xy


def u_value(t, S):
    goods = [g for g in range(8) if (S >> g) & 1]
    if not goods:
        return 0
    if len(goods) == 1:
        return 1
    return max(pair_value(t, TYPE[g], TYPE[h]) for g, h in combinations(goods, 2))


def v_value(t, S):
    U, V = [z for z in "ABC" if z != t]
    types = [TYPE[g] for g in range(8) if (S >> g) & 1]
    if U in types and V in types and "x" in types:
        return 7
    return u_value(t, S)


def tables(fun):
    return [[fun(t, S) for S in range(256)] for t in AGENT_TYPE]


def show(alloc):
    B = [[] for _ in range(3)]
    for g, o in enumerate(alloc):
        B[o].append(NAMES[g])
    return " | ".join("".join(b) or "-" for b in B)


def restrict_delete(tab, m, d):
    """Instance on m-1 goods with good d deleted: v'(S) = v(S) for S not containing d."""
    keep = [g for g in range(m) if g != d]
    out = []
    for S in range(1 << (m - 1)):
        T = 0
        for t, g in enumerate(keep):
            if (S >> t) & 1:
                T |= 1 << g
        out.append(tab[T])
    return out


def restrict_merge(tab, m, g1, g2):
    """Merge goods g1 < g2 into one good: v'(S) = v(S with the merged good expanded)."""
    keep = [g for g in range(m) if g != g2]
    out = []
    for S in range(1 << (m - 1)):
        T = 0
        for t, g in enumerate(keep):
            if (S >> t) & 1:
                T |= 1 << g
                if g == g1:
                    T |= 1 << g2
        out.append(tab[T])
    return out


def main():
    U = tables(u_value)
    V = tables(v_value)
    for name, tabs in (("u", U), ("v", V)):
        for i in range(3):
            err = check_normalized_monotone(8, tabs[i])
            assert err is None, (name, i, err)
    print("u and v: normalized and monotone for all three agents")
    for i in range(3):
        R = relevant_goods(8, V[i])
        print(f"agent {'abc'[i]}: relevant goods {[NAMES[g] for g in R]}  (k = {len(R)})")
    eu = all_efx0(3, 8, U)
    print(f"EFX0 allocations under u: {len(eu)}")
    shapes = sorted(set(show(a) for a in eu))
    for s in shapes[:12]:
        print("   ", s)
    ev = all_efx0(3, 8, V)
    print(f"EFX0 allocations under v: {len(ev)}   (paper, Theorem 3.4: none)")
    assert not ev
    # modifications: delete a good / merge two goods (both give m = 7, where Theorem 1.2 of the
    # paper says an EFX allocation always exists); confirm directly.
    for d in range(8):
        T = [restrict_delete(V[i], 8, d) for i in range(3)]
        assert all_efx0(3, 7, T, limit=1), d
    for g1, g2 in combinations(range(8), 2):
        T = [restrict_merge(V[i], 8, g1, g2) for i in range(3)]
        assert all_efx0(3, 7, T, limit=1), (g1, g2)
    print("deleting any one good, or merging any two goods, leaves an instance with an EFX0 allocation")


if __name__ == "__main__":
    main()
