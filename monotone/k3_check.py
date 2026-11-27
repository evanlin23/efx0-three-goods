"""Exhaustive check of the per-agent lemma behind Theorem M3 (monotone/k3.md).

Lemma S3. Let v be a nondegenerate monotone valuation (all 2^r values distinct, hence strictly
increasing under inclusion) on r <= 3 relevant goods. Then there is an additive valuation w on the
same goods, all values positive, such that for every pair of DISJOINT subsets A, B:
        v(A) < v(B)  <=>  w(A) < w(B).

Check: enumerate every linear extension of the Boolean lattice 2^[r] (r = 1, 2, 3; these are the
nondegenerate monotone orders up to the actual numbers), and compare its disjoint-pair comparisons
with those of the explicit surrogate of monotone/k3.md: with the singletons ranked
s1 > s2 > s3,  w = (4, 3, 2) if v({s1}) < v({s2, s3}) ("balanced") and w = (6, 3, 2) otherwise
("top-heavy"); w = (2, 1) for r = 2 and w = (1) for r = 1.

Also prints a nondegenerate monotone order on r = 4 goods whose disjoint comparisons no additive
valuation has (so Lemma S3 fails at r = 4).

Usage: python3 monotone/k3_check.py
"""


def linear_extensions(r):
    """All linear orders of the subsets of [r] (bitmasks) extending inclusion, as rank lists."""
    N = 1 << r
    preds = [[T for T in range(N) if T != S and (T & S) == T] for S in range(N)]
    out = []
    order = []
    placed = [False] * N

    def rec():
        if len(order) == N:
            rank = [0] * N
            for pos, S in enumerate(order):
                rank[S] = pos
            out.append(rank)
            return
        for S in range(N):
            if not placed[S] and all(placed[T] for T in preds[S]):
                placed[S] = True
                order.append(S)
                rec()
                order.pop()
                placed[S] = False

    rec()
    return out


def disjoint_signature(r, val):
    """Tuple of comparisons val(A) < val(B) over ordered disjoint pairs (A, B), A != B."""
    N = 1 << r
    sig = []
    for A in range(N):
        for B in range(N):
            if A != B and not (A & B):
                sig.append(val[A] < val[B])
    return tuple(sig)


def additive_table(r, w):
    return [sum(w[g] for g in range(r) if (S >> g) & 1) for S in range(1 << r)]


def surrogate(r, rank):
    singles = sorted(range(r), key=lambda g: -rank[1 << g])  # s1 > s2 > ...
    w = [0] * r
    if r == 1:
        w[singles[0]] = 1
    elif r == 2:
        w[singles[0]], w[singles[1]] = 2, 1
    else:
        s1, s2, s3 = singles
        balanced = rank[1 << s1] < rank[(1 << s2) | (1 << s3)]
        w[s1], w[s2], w[s3] = (4, 3, 2) if balanced else (6, 3, 2)
    return w


def main():
    for r in (1, 2, 3):
        exts = linear_extensions(r)
        bad = 0
        for rank in exts:
            w = surrogate(r, rank)
            if disjoint_signature(r, rank) != disjoint_signature(r, additive_table(r, w)):
                bad += 1
        print(f"r = {r}: {len(exts)} nondegenerate monotone orders, "
              f"{bad} whose disjoint comparisons differ from the additive surrogate")
        assert bad == 0
    # r = 4: Lemma S3 fails. Example: v on {a, b, c, d} (bits 0..3), singletons a > b > c > d,
    # but v({c, d}) > v({a, b}); any additive w with w(a) > w(c) and w(b) > w(d) has w(ab) > w(cd).
    r = 4
    val = [None] * 16
    order = [0b0000, 0b1000, 0b0100, 0b0010, 0b0001, 0b0011, 0b0101, 0b1001, 0b0110,
             0b1010, 0b1100, 0b0111, 0b1011, 0b1101, 0b1110, 0b1111]
    for pos, S in enumerate(order):
        val[S] = pos
    assert sorted(order) == list(range(16))
    assert all(val[S] < val[S | (1 << g)] for S in range(16) for g in range(4) if not (S >> g) & 1)
    assert val[1] > val[2] > val[4] > val[8] and val[0b1100] > val[0b0011]
    name = lambda S: "".join("abcd"[g] for g in range(4) if (S >> g) & 1) or "{}"
    print("r = 4: the monotone order", " < ".join(name(S) for S in order),
          "has v(a) > v(b) > v(c) > v(d) and v(cd) > v(ab), so no additive valuation has its "
          "disjoint comparisons")

if __name__ == "__main__":
    main()
