"""Independent replay of the refutation of Conjecture OC1-H (k4/ttc.md §8, attempts/k4-ttc-head-owner.md), written from
the definitions only: no SAT, no de_free / ttclib / sdclib code.

Instance (n = 6, m = 10, found by k4/ttc/head_bign_climb.py; case 0 of hd_fail_check.py) and order (0, 1, ..., 5):
  1. serial dictatorship (ties by good index; values here are distinct per agent);
  2. the picks have no one-absorber completion (every assignment of the junk in which at most one agent receives two
     or more junk goods, checked against the raw EFX0 definition);
  3. every improving chain x_0, ..., x_t (t >= 1): distinct agents; H_0 inside (J + B_{x_t}) and R_{x_0} with
     v_{x_0}(H_0) > v_{x_0}(B_{x_0}); H_i inside J and R_{x_i}, pairwise disjoint and disjoint from H_0, with
     v_{x_i}(B_{x_{i-1}} + H_i) > v_{x_i}(B_{x_i}); x_0 takes H_0, x_i takes B_{x_{i-1}} + H_i, the rest of B_{x_t}
     becomes junk.  For each: is there a completion in which every agent other than the head x_t receives at most one
     junk good (the head absorbs), EFX0 by the raw definition?  The claim: never.  Also reported: chains with a
     one-absorber completion for some absorber (OC1 holds), and which absorbers work.

    python3 k4/ttc/refute_head.py [case]   (case 0 or 1)"""
import itertools, sys

CASES = [
    ([[0, 2, 3, 1], [1, 4, 5, 9], [1, 2, 3, 9], [1, 6, 7, 8], [3, 6, 9], [1, 3, 6, 9]],
     [[2, 7, 8, 5], [2, 9, 5, 10], [10, 2, 6, 5], [8, 7, 1, 5], [10, 1, 2], [10, 9, 3, 1]], 10),
    ([[0, 2, 3, 1], [1, 4, 5, 9], [1, 2, 0, 8], [1, 6, 7, 8], [3, 6, 9], [1, 3, 6, 9]],
     [[2, 7, 8, 5], [5, 6, 4, 9], [13, 5, 4, 8], [10, 7, 1, 4], [7, 2, 10], [10, 6, 4, 1]], 10),
]


def main(case):
    sets, vals, m = CASES[case]
    n = len(sets); v = [dict(zip(s, x)) for s, x in zip(sets, vals)]
    val = lambda i, S: sum(v[i].get(g, 0) for g in S)

    def efx0(X):
        for i in range(n):
            own = val(i, X[i])
            for j in range(n):
                if i != j:
                    tot = val(i, X[j])
                    if any(tot - v[i].get(g, 0) > own for g in X[j]):
                        return False
        return True

    def completions(B, absorbers):
        """completions of the bases B in which every agent outside `absorbers` gets at most one junk good
        (absorbers: a set of agents allowed any number; for 'one absorber' call once per candidate)"""
        J = [g for g in range(m) if not any(g in b for b in B)]
        def rec(k, X, used):
            if k == len(J):
                yield [list(x) for x in X]; return
            g = J[k]
            for a in range(n):
                if a not in absorbers and a in used:
                    continue
                X[a].append(g)
                yield from rec(k + 1, X, used | ({a} if a not in absorbers else set()))
                X[a].pop()
        yield from rec(0, [list(b) for b in B], frozenset())

    def has_completion(B, absorber):
        return any(efx0(X) for X in completions(B, {absorber} if absorber is not None else set()))

    # 1. serial dictatorship in the order 0..n-1
    left = set(range(m)); Y = []
    for i in range(n):
        av = [g for g in sets[i] if g in left]
        if av:
            g = max(av, key=lambda h: (v[i][h], -h)); Y.append(g); left.discard(g)
        else:
            Y.append(None)
    B0 = [[y] if y is not None else [] for y in Y]
    J0 = [g for g in range(m) if g not in Y]
    print('case', case, 'sets', sets, 'vals', vals)
    print('picks', Y, 'junk', J0)
    # 2. no one-absorber completion of the picks
    pick_ok = any(has_completion(B0, o) for o in list(range(n)) + [None])
    print('picks have a one-absorber completion:', pick_ok)
    assert not pick_ok
    # 3. every improving chain
    def subsets(xs):
        for r in range(len(xs) + 1):
            yield from itertools.combinations(xs, r)
    nch = 0; head_ok = []; oc1 = []
    for t in range(1, n):
        for path in itertools.permutations(range(n), t + 1):
            x0, xt = path[0], path[-1]
            if any(not B0[path[i - 1]] for i in range(1, t + 1)):
                continue               # x_i takes B_{x_{i-1}}: every passed base is a pick (an empty base passes nothing)
            def rec(i, used, Hs):
                if i > t:
                    yield dict(Hs); return
                pool = [g for g in J0 if g not in used and v[path[i]].get(g, 0) > 0]
                for H in subsets(pool):
                    if val(path[i], B0[path[i - 1]] + list(H)) > val(path[i], B0[path[i]]):
                        yield from rec(i + 1, used | set(H), {**Hs, i: H})
            for Hs in rec(1, set(), {}):
                used = set(g for H in Hs.values() for g in H)
                pool0 = [g for g in J0 + B0[xt] if g not in used and v[x0].get(g, 0) > 0]
                for H0 in subsets(pool0):
                    if not H0 or val(x0, H0) <= val(x0, B0[x0]):
                        continue
                    B = [list(b) for b in B0]
                    B[x0] = list(H0)
                    for i in range(1, t + 1):
                        B[path[i]] = B0[path[i - 1]] + list(Hs[i])
                    nch += 1
                    if has_completion(B, xt):
                        head_ok.append((path, B))
                    owners = [o for o in range(n) if o != xt and has_completion(B, o)]
                    if owners:
                        oc1.append((path, B, owners))
    print('improving chains with t >= 1:', nch)
    print('chains with a completion in which the head absorbs:', len(head_ok))
    print('chains with a one-absorber completion for some other absorber (OC1):', len(oc1))
    for path, B, owners in oc1[:6]:
        print('   chain', path, 'bases', B, 'absorbers that work', owners)
    assert not head_ok and oc1
    print('REFUTED: OC1-H fails on case', case, '(OC1 holds)')


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
