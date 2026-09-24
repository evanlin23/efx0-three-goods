"""Brute-force cross-check of the table in proofs/real_values.md (L12). Evidence only, not a proof.

For every agent profile with at most three relevant goods and values in 1..N (N = 12 by default), plus
every rational profile with denominators up to 6 over the same range, build the natural-number valuation
w of the L12 table and check that v and w order all pairs of subsets of the relevant goods identically
(v(S) <= v(T) iff w(S) <= w(T)), and that both have the same relevant goods. Zero-valued goods are left
out: they contribute 0 to both v and w. Run: python tools/audit_l12.py [N]
"""
import itertools
import sys
from fractions import Fraction


def table_w(vals):
    """The L12 representative for the positive values `vals` (a list of length 0..3)."""
    order = sorted(range(len(vals)), key=lambda k: -vals[k])  # a >= b >= c
    s = [vals[k] for k in order]
    if len(s) == 0:
        rep = []
    elif len(s) == 1:
        rep = [1]
    elif len(s) == 2:
        rep = [2, 1] if s[0] > s[1] else [1, 1]
    else:
        a, b, c = s
        sign = (a > b + c) - (a < b + c)
        if a > b > c:
            rep = {-1: [4, 3, 2], 0: [3, 2, 1], 1: [5, 2, 1]}[sign]
        elif a == b > c:
            assert sign == -1
            rep = [2, 2, 1]
        elif a > b == c:
            rep = {-1: [3, 2, 2], 0: [2, 1, 1], 1: [3, 1, 1]}[sign]
        else:
            rep = [1, 1, 1]
    w = [0] * len(vals)
    for pos, k in enumerate(order):
        w[k] = rep[pos]
    return w


def same_order(v, w):
    subsets = [S for r in range(len(v) + 1) for S in itertools.combinations(range(len(v)), r)]
    for S in subsets:
        for T in subsets:
            if (sum(v[k] for k in S) <= sum(v[k] for k in T)) != (sum(w[k] for k in S) <= sum(w[k] for k in T)):
                return False
    return all(x > 0 for x in w)


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    grid = sorted({Fraction(p, q) for q in range(1, 7) for p in range(1, N * q + 1)})
    checked = 0
    for r in range(4):
        pools = [range(1, N + 1)] if r == 3 else [grid]
        for pool in pools:
            for vals in itertools.product(pool, repeat=r):
                if not same_order(list(vals), table_w(list(vals))):
                    print("MISMATCH", vals, table_w(list(vals)))
                    sys.exit(1)
                checked += 1
    # Three goods on the rational grid, restricted to a <= 4 to keep the run short.
    small = [x for x in grid if x <= 4]
    for vals in itertools.product(small, repeat=3):
        if not same_order(list(vals), table_w(list(vals))):
            print("MISMATCH", vals, table_w(list(vals)))
            sys.exit(1)
        checked += 1
    print(f"L12 table: {checked} profiles checked, v and w order all subset pairs identically")


if __name__ == "__main__":
    main()
