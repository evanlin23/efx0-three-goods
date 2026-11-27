"""Reproduces the smallest counterexamples to "one pick per bundle" (attempts/kgen-n3-opb.md, kgen/n3.md §14.1-§14.2):
lists every EFX0 allocation (raw definition, every good removable) with its pick placement, and whether some
allocation has one pick per bundle with every moved agent gaining (v_i(X_i) > v_i(y_i)).

    python3 kgen/opb_cex.py"""
import itertools

CEX = [('n = 3, k = 4 core, m = 5 (OPB3)', [[0, 1, 2, 4], [1, 3, 4], [2, 3, 4]], [[3, 6, 10, 2], [4, 2, 3], [4, 2, 3]], (1, 2, 0)),
       ('n = 4, k = 4 core, m = 7 (OPB4; the OC1^max counterexample)', [[0, 1, 2, 5], [1, 2, 5, 6], [3, 4, 5, 6], [3, 4, 6]],
        [[2, 10, 4, 7], [10, 3, 4, 8], [3, 5, 6, 7], [3, 2, 4]], (0, 3, 2, 1))]

for name, sets, vals, order in CEX:
    n = len(sets); m = 1 + max(g for S in sets for g in S); v = [[0] * m for _ in range(n)]
    for i in range(n):
        for g, x in zip(sets[i], vals[i]): v[i][g] = x
    left = set(range(m)); y = [None] * n
    for i in order:
        g = max((h for h in left if v[i][h] > 0), key=lambda h: v[i][h]); y[i] = g; left.discard(g)
    P = set(y); found = False; cnt = 0
    print('%s: sets %s, values %s, order %s, picks %s' % (name, sets, vals, order, y))
    for q in itertools.product(range(n), repeat=m):
        X = [{g for g in range(m) if q[g] == i} for i in range(n)]
        ok = all(sum(v[i][g] for g in X[i]) >= sum(v[i][h] for h in X[j] if h != g)
                 for i in range(n) for j in range(n) if j != i for g in X[j])
        if not ok: continue
        cnt += 1; opb = all(len(B & P) == 1 for B in X)
        gain = opb and all(sum(v[i][g] for g in X[i]) > v[i][y[i]] for i in range(n) if y[i] not in X[i])
        found |= gain
        print('   EFX0', [sorted(b) for b in X], 'picks per bundle', [sorted(b & P) for b in X], 'OPB with gains' if gain else '')
    print('   %d EFX0 allocations; one pick per bundle with every moved agent gaining: %s' % (cnt, found))
