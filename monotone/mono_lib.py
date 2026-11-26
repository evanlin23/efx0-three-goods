"""Shared helpers for the monotone bounded-relevance workstream (proof/monotone-k).

An instance is (n, m, vals) where vals[i] is a function from a frozenset/bitmask of goods
(over all m goods) to a nonnegative number; we store it as a full table of length 2^m
(m <= 12 here) so that every check below uses the raw definitions only:

  * normalized: v(empty) = 0
  * monotone:   S subset T  =>  v(S) <= v(T)
  * relevant goods of i: R_i = {g : v_i(S + g) > v_i(S) for some S}   (the goods that change i's value)
  * EFX0 (all goods, including value-0 ones): for all i != j and every g in X_j,
        v_i(X_i) >= v_i(X_j minus g).

Nothing here uses additivity or the L5 ordinal model.
"""
from itertools import product


def popcount(x):
    return bin(x).count("1")


def check_normalized_monotone(m, table):
    """table: list of 2^m numbers. Returns None if fine, else a witness string."""
    if table[0] != 0:
        return "v(empty) != 0"
    for S in range(1 << m):
        if table[S] < 0:
            return f"negative value at {S}"
        for g in range(m):
            if not (S >> g) & 1:
                if table[S | (1 << g)] < table[S]:
                    return f"not monotone: v({S}) > v({S | (1 << g)})"
    return None


def relevant_goods(m, table):
    R = []
    for g in range(m):
        bit = 1 << g
        if any(table[S | bit] > table[S] for S in range(1 << m) if not S & bit):
            R.append(g)
    return R


def bundles_of(alloc, n):
    """alloc: tuple of length m with owner of each good -> list of bitmasks."""
    B = [0] * n
    for g, o in enumerate(alloc):
        B[o] |= 1 << g
    return B


def efx0_violation(n, m, tables, B):
    """B: list of n bitmasks (a complete allocation). Returns None if EFX0, else (i, j, g)."""
    for i in range(n):
        own = tables[i][B[i]]
        for j in range(n):
            if j == i or B[j] == 0:
                continue
            Xj = B[j]
            for g in range(m):
                if (Xj >> g) & 1 and tables[i][Xj & ~(1 << g)] > own:
                    return (i, j, g)
    return None


def all_efx0(n, m, tables, limit=None):
    """Every complete EFX0 allocation (as owner tuples), by brute force over n^m allocations."""
    out = []
    for alloc in product(range(n), repeat=m):
        B = bundles_of(alloc, n)
        if efx0_violation(n, m, tables, B) is None:
            out.append(alloc)
            if limit is not None and len(out) >= limit:
                break
    return out


def table_from_function(m, f):
    return [f(S) for S in range(1 << m)]


def table_from_restricted(m, R, sub):
    """R: list of goods; sub: list of 2^|R| values indexed by bitmask over positions in R.
    Returns the full 2^m table with v(S) = sub[S cap R]."""
    pos = {g: t for t, g in enumerate(R)}
    out = []
    for S in range(1 << m):
        idx = 0
        for g in R:
            if (S >> g) & 1:
                idx |= 1 << pos[g]
        out.append(sub[idx])
    return out
