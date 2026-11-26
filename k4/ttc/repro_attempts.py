"""Reproduce the smallest failing configurations of the failed ideas of k4/ttc.md (attempts/k4-ttc-*.md).  Every
claim is re-checked by brute force from the raw EFX0 definition (no SAT, no shared completion code); ttclib is used
only to run the mechanism (YRMH-IGYT) and to list the improving chains.

  python3 k4/ttc/repro_attempts.py

(a) attempts/k4-ttc-priority-rules.md: r428 (n = 3, m = 5).  The best single TTC rule (minval/minval, priority =
    reverse order, repeated single trades) makes no trade from the picks of order (0, 1, 2), which have no
    one-absorber completion; one improving chain repairs them (OC1 holds).
(b) attempts/k4-ttc-local-validity.md: T3 (n = 3, m = 6).  From picks (0, 1, 4) no chain whose result is valid (every
    wanted good held alone) repairs; from picks (0, 4, 1) a valid, threat-free chain result does not repair.
(c) not an attempt: an independent brute-force cross-check of Conjecture MDP (k4/ttc.md §7) on the start where a
    first, wrong version of displace.py's one-path test reported a counterexample: rt4-n5m10-chain (n = 5,
    m = 10), picks (8, 3, 9, 5, 7).  The fewest displaced picks over the complete EFX0 allocations that value-dominate
    the picks is 3, attained by 36 allocations, and every one of them is one-path.
(d) attempts/k4-ttc-min-displacement.md: r617 (n = 4, m = 8), picks (7, 3, 5, 4).  The fewest displaced picks over the
    dominating complete EFX0 allocations is 2, and some allocation attaining it is not one-path (two separate pool
    swaps); some other allocation attaining it is one-path."""
import itertools, sys
import ttclib as T


def efx0(v, X):
    n = len(X)
    for i in range(n):
        own = sum(v[i].get(g, 0) for g in X[i])
        for j in range(n):
            if i == j:
                continue
            tot = sum(v[i].get(g, 0) for g in X[j])
            for g in X[j]:
                if tot - v[i].get(g, 0) > own:
                    return False
    return True


def completions(n, base, A=None):
    """every complete allocation keeping the bases; with A = 1, at most one agent gets two or more junk goods"""
    J = [g for g, a in enumerate(base) if a < 0]
    for asg in itertools.product(range(n), repeat=len(J)):
        if A is not None:
            cnt = [0] * n
            for a in asg:
                cnt[a] += 1
            if sum(1 for c in cnt if c >= 2) > A:
                continue
        X = [[g for g, a in enumerate(base) if a == i] for i in range(n)]
        for g, a in zip(J, asg):
            X[a].append(g)
        yield X


def one_absorber(v, n, base):
    return any(efx0(v, X) for X in completions(n, base, 1))


def part_a():
    sets = [[0, 1, 3, 4], [0, 2, 3, 4], [1, 2, 4]]; vals = [[4, 3, 6, 8], [2, 10, 3, 6], [2, 3, 4]]; m = 5
    E = T.Enc(sets, vals, m); v = E.v; pi = [0, 1, 2]
    Y = tuple(T.sd(E, pi)[0]); b = T.base_of(E, Y)
    print('(a) r428', sets, vals, 'order', pi, 'picks', Y)
    print('    picks have a one-absorber completion (brute force):', one_absorber(v, 3, b))
    b2, k, ok = T.run_mech(E, b, pi, 'minval/minval', 'rev', 'rep')
    print('    best TTC rule (minval/minval, rev, rep): trades', k, 'end state', T.bundles(E, b2),
          'one-absorber completion (brute force):', one_absorber(v, 3, b2))
    rep = [T.bundles(E, s) for s in set(T.DF.iter_chains(E, b)) if one_absorber(v, 3, s)]
    print('    repairing improving chains (brute-force completion):', rep)
    assert not one_absorber(v, 3, b) and not one_absorber(v, 3, b2) and rep


def valid(E, base):
    B = T.bundles(E, base); n = E.n
    hold = [T.val(E, i, B[i]) for i in range(n)]
    for i in range(n):
        for g in E.R[i]:
            if g not in B[i] and E.v[i][g] > hold[i] and not any(B[j] == [g] for j in range(n)):
                return False
    return True


def threat_free(E, base):
    B = T.bundles(E, base); n = E.n
    for i in range(n):
        own = T.val(E, i, B[i])
        for j in range(n):
            if i != j and len(B[j]) >= 2 and any(T.val(E, i, [h for h in B[j] if h != g]) > own for g in B[j]):
                return False
    return True


def part_b():
    sets = [[5, 0, 4, 2], [3, 1, 4], [4, 1, 3, 0]]; vals = [[1, 38, 36, 6], [12, 22, 30], [28, 20, 12, 38]]; m = 6
    E = T.Enc(sets, vals, m); v = E.v
    print('(b) T3', sets, vals)
    for Y in ((0, 1, 4), (0, 4, 1)):
        b = T.base_of(E, Y)
        rows = []
        for s in set(T.DF.iter_chains(E, b)):
            rows.append((T.bundles(E, s), valid(E, s), threat_free(E, s), one_absorber(v, 3, s)))
        print('    picks', Y, 'one-absorber completion:', one_absorber(v, 3, b))
        for r in sorted(rows):
            print('      chain result', r[0], 'valid', r[1], 'threat-free', r[2], 'repairs', r[3])
        if Y == (0, 1, 4):
            assert any(r[3] for r in rows) and not any(r[1] and r[3] for r in rows)
        else:
            assert any(r[1] and r[2] and not r[3] for r in rows)


def part_c(sets=None, vals=None, n=5, m=10, Y=(8, 3, 9, 5, 7), label='(c) rt4-n5m10-chain', expect=(3, False)):
    sets = sets or [[0, 2, 4, 8], [1, 3, 8, 9], [3, 4, 8, 9], [5, 6, 7, 9], [5, 6, 7, 9]]
    vals = vals or [[2, 6, 3, 10], [2, 8, 4, 3], [10, 2, 6, 3], [4, 2, 3, 8], [4, 2, 3, 8]]
    v = [dict(zip(s, x)) for s, x in zip(sets, vals)]
    u = [v[i][Y[i]] for i in range(n)]
    print(label, sets, vals, 'picks', Y)
    def dominating(X):
        return all(sum(v[i].get(g, 0) for g in X[i]) >= u[i] for i in range(n))
    best = None; witness = []
    for keep in range(n, n - 4, -1):
        found = []
        for K in itertools.combinations(range(n), keep):
            base = [-1] * m
            for i in K:
                base[Y[i]] = i
            for X in completions(n, base):
                if sum(1 for i in range(n) if Y[i] not in X[i]) != n - keep:
                    continue
                if dominating(X) and efx0(v, X):
                    found.append(X)
        if found:
            best = n - keep; witness = found; break
    print('    fewest displaced agents over dominating EFX0 allocations (brute force):', best,
          '; allocations attaining it:', len(witness))
    def one_path(holder):
        disp = [j for j in range(n) if holder[j] != j]; D = set(disp)
        for xt in disp:          # the end's pick becomes junk and may lie anywhere
            nxt = {j: holder[j] for j in disp if j != xt and holder[j] in D}
            if len(nxt) != len(D) - 1:
                continue
            starts = [j for j in D if j not in nxt.values()]
            if len(starts) != 1:
                continue
            cur, seen = starts[0], {starts[0]}
            while cur in nxt and nxt[cur] not in seen:
                cur = nxt[cur]; seen.add(cur)
            if seen == D and cur == xt:
                return True
        return not disp
    bad = []
    for X in witness:
        holder = {j: [i for i in range(n) if Y[j] in X[i]][0] for j in range(n)}
        if not one_path(holder):
            bad.append((X, holder))
    print('    minimal allocations that are not one-path:', len(bad), 'of', len(witness))
    if bad:
        X, h = bad[0]
        print('      e.g.', X, 'pick owner -> holder', h)
    assert best == expect[0] and bool(bad) == expect[1] and len(bad) < len(witness)


def part_d():
    part_c([[0, 2, 6, 7], [1, 3, 6, 7], [3, 4, 5, 7], [4, 5, 7]], [[5, 3, 6, 7], [6, 7, 3, 5], [5, 3, 6, 7], [2, 4, 3]],
           4, 8, (7, 3, 5, 4), '(d) r617', (2, True))


if __name__ == '__main__':
    part_a(); part_b(); part_c(); part_d()
    print('(a), (b), (d) reproduced; (c) MDP confirmed on rt4-n5m10-chain')
