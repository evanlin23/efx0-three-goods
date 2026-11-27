"""Independent replay (no SAT, no shared code): value domination fails for partial EFX0 allocations with two two-good
bundles (k4/sdc.md §28).  Instance GM4-A of the screen set (n = 4, m = 7, a k = 4 core with a strict profile).  The
partial allocation X = ({0,2}, {1,4}, {5}, {6}) (good 3 unallocated) is EFX0, and no complete EFX0 allocation gives
every agent at least its value under X.  Brute force over all 4^7 complete allocations.

    python3 k4/sdc/refute_md2.py"""
import itertools

SETS = [[0, 2, 5, 6], [1, 4, 5, 6], [2, 3, 5, 6], [3, 4, 5, 6]]
VALS = [[3, 6, 2, 10], [1, 6, 8, 4], [2, 7, 8, 4], [6, 3, 4, 8]]
X = [[0, 2], [1, 4], [5], [6]]
N, M = 4, 7
val = [dict(zip(S, V)) for S, V in zip(SETS, VALS)]


def worth(i, B):
    return sum(val[i].get(g, 0) for g in B)


def efx0(bundles):
    for i in range(N):
        mine = worth(i, bundles[i])
        for j in range(N):
            if j != i and any(worth(i, [g for g in bundles[j] if g != h]) > mine for h in bundles[j]):
                return False
    return True


if __name__ == '__main__':
    print('$ python3 k4/sdc/refute_md2.py')
    u = [worth(i, X[i]) for i in range(N)]
    print('X =', X, 'values', u, 'X is partial EFX0:', efx0(X), 'unallocated:', sorted(set(range(M)) - set(g for B in X for g in B)))
    n_efx = n_dom = 0
    for a in itertools.product(range(N), repeat=M):
        B = [[g for g in range(M) if a[g] == i] for i in range(N)]
        if not efx0(B): continue
        n_efx += 1
        if all(worth(i, B[i]) >= u[i] for i in range(N)):
            n_dom += 1; print('dominating complete EFX0 allocation:', B)
    print('complete EFX0 allocations:', n_efx, '; of these value-dominating X:', n_dom)
    print('REFUTED: two-pair domination fails' if n_dom == 0 and n_efx > 0 else 'not refuted')
    # the matching form: every maximal matching (each agent at most one good it values) is dominated
    bad = 0; tot = 0
    for Y in itertools.product(*[S + [None] for S in SETS]):
        g = [y for y in Y if y is not None]
        if len(g) != len(set(g)): continue
        tot += 1; t = [val[i][Y[i]] if Y[i] is not None else 0 for i in range(N)]
        ok = False
        for a in itertools.product(range(N), repeat=M):
            B = [[h for h in range(M) if a[h] == i] for i in range(N)]
            if all(worth(i, B[i]) >= t[i] for i in range(N)) and efx0(B): ok = True; break
        bad += not ok
    print('matchings:', tot, '; not value-dominated:', bad)
