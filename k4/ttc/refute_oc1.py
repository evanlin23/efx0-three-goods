"""Independent replay of a counterexample to Conjecture OC1 (k4/sdc.md §29), written from the definitions only: no SAT,
no de_free / ttclib / sdclib / oc_absorb code.  Found by k4/ttc/head_bign_climb.py ... ends seeded
(results/k4_ttc/head_bign_climb_ends_seeded.log), climbing from the OC1-H counterexample of refute_head.py.

OC1: for every order, the serial-dictatorship picks have a one-absorber completion (an EFX0 allocation keeping every
pick, in which at most one agent receives two or more unpicked goods), or after one improving move the bases have one.
Moves (as in k4/sdc/de_free.py, the repository's test of OC1, oc_absorb.py):
  - addition (t = 0): x_0 adds a set H_0 of junk goods it values (H_0 nonempty) to its base;
  - chain (t >= 1): distinct x_0, ..., x_t; x_0 takes H_0 inside (J + B_{x_t}) cap R_{x_0} with
    v(H_0) > v(B_{x_0}); x_i takes B_{x_{i-1}} + H_i, H_i inside J cap R_{x_i}, with v(B_{x_{i-1}} + H_i) > v(B_{x_i});
    the H's pairwise disjoint; the rest of B_{x_t} becomes junk;
  - ring (k >= 2): distinct w_0, ..., w_{k-1}; each w_{s+1} takes B_{w_s} + H_{s+1} (indices mod k), H inside J and
    the receiver's relevant goods, disjoint, each receiver strictly better off.
(de_free caps |H| <= 4 and bases at <= 4 goods; with |R_i| <= 4 the H's need no cap, and the replay applies no base
cap, so it checks a superset of de_free's moves.)
The replay checks, by brute force over completions against the raw EFX0 definition:
  1. the picks of the order have no one-absorber completion;
  2. no move gives bases with a one-absorber completion  ->  OC1 fails for this order;
  and reports, for context: the free completion (any number of absorbers) of the picks and after each move (OC),
  how many moves exist, and (by brute force over all allocations) whether a complete EFX0 allocation exists at all
  and whether one value-dominates the picks (MD).

    python3 k4/ttc/refute_oc1.py [FILE.json [INDEX]]   (default: the instance below)"""
import itertools, sys, json

DEFAULT = {"sets": [[0, 2, 3, 1], [1, 4, 5, 9], [1, 2, 0, 8], [1, 6, 7, 8], [3, 6, 9], [1, 3, 6, 9]],
           "vals": [[2, 7, 8, 3], [3, 6, 4, 9], [12, 2, 4, 8], [12, 6, 3, 4], [7, 2, 10], [7, 8, 4, 1]],
           "m": 10, "order": [0, 1, 2, 3, 4, 5]}


def main(d):
    sets, vals, m, order = d['sets'], d['vals'], d['m'], d['order']
    n = len(sets); v = [dict(zip(s, x)) for s, x in zip(sets, vals)]
    assert all(len(s) <= 4 for s in sets) and all(x > 0 for vv in vals for x in vv)
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

    def junk_of(B):
        held = set(g for b in B for g in b)
        return [g for g in range(m) if g not in held]

    def one_absorber(B):
        J = junk_of(B)
        for o in range(n):
            def rec(k, X, used):
                if k == len(J):
                    return efx0(X)
                g = J[k]
                for a in range(n):
                    if a != o and a in used:
                        continue
                    X[a].append(g)
                    ok = rec(k + 1, X, used | ({a} if a != o else set()))
                    X[a].pop()
                    if ok:
                        return True
                return False
            if rec(0, [list(b) for b in B], frozenset()):
                return True
        return False

    def free(B):
        J = junk_of(B)
        for asg in itertools.product(range(n), repeat=len(J)):
            X = [list(b) for b in B]
            for g, a in zip(J, asg):
                X[a].append(g)
            if efx0(X):
                return True
        return False

    def subsets(xs):
        for r in range(len(xs) + 1):
            yield from itertools.combinations(xs, r)

    # serial dictatorship
    left = set(range(m)); Y = [None] * n
    for i in order:
        av = [g for g in sets[i] if g in left]
        if av:
            g = max(av, key=lambda h: (v[i][h], -h)); Y[i] = g; left.discard(g)
    B0 = [[y] if y is not None else [] for y in Y]; J0 = junk_of(B0)
    print('sets', sets, 'vals', vals, 'm', m)
    print('order', order, 'picks', Y, 'junk', J0)
    p1 = one_absorber(B0); pf = free(B0)
    print('1. picks: one-absorber completion', p1, '| free completion', pf)
    assert not p1

    moves = []
    # additions
    for x in range(n):
        for H in subsets([g for g in J0 if v[x].get(g, 0) > 0]):
            if H:
                B = [list(b) for b in B0]; B[x] = B0[x] + list(H); moves.append(('add', (x,), B))
    # chains
    for t in range(1, n):
        for path in itertools.permutations(range(n), t + 1):
            if any(not B0[path[i - 1]] for i in range(1, t + 1)):
                continue
            def rec(i, used, Hs):
                if i > t:
                    yield dict(Hs); return
                pool = [g for g in J0 if g not in used and v[path[i]].get(g, 0) > 0]
                for H in subsets(pool):
                    if val(path[i], B0[path[i - 1]] + list(H)) > val(path[i], B0[path[i]]):
                        yield from rec(i + 1, used | set(H), {**Hs, i: H})
            for Hs in rec(1, set(), {}):
                used = set(g for H in Hs.values() for g in H)
                pool0 = [g for g in J0 + B0[path[-1]] if g not in used and v[path[0]].get(g, 0) > 0]
                for H0 in subsets(pool0):
                    if not H0 or val(path[0], H0) <= val(path[0], B0[path[0]]):
                        continue
                    B = [list(b) for b in B0]; B[path[0]] = list(H0)
                    for i in range(1, t + 1):
                        B[path[i]] = B0[path[i - 1]] + list(Hs[i])
                    moves.append(('chain', path, B))
    # rings
    for k in range(2, n + 1):
        for cyc in itertools.permutations(range(n), k):
            if cyc[0] != min(cyc) or any(not B0[w] for w in cyc):
                continue
            def rec(s, used, Hs):
                if s == k:
                    yield dict(Hs); return
                rcv, giver = cyc[(s + 1) % k], cyc[s]
                pool = [g for g in J0 if g not in used and v[rcv].get(g, 0) > 0]
                for H in subsets(pool):
                    if val(rcv, B0[giver] + list(H)) > val(rcv, B0[rcv]):
                        yield from rec(s + 1, used | set(H), {**Hs, rcv: H})
            for Hs in rec(0, set(), {}):
                B = [list(b) for b in B0]
                for s in range(k):
                    rcv, giver = cyc[(s + 1) % k], cyc[s]
                    B[rcv] = B0[giver] + list(Hs[rcv])
                moves.append(('ring', cyc, B))
    print('2. improving moves: %d (additions %d, chains %d, rings %d)' % (
        len(moves), sum(1 for x in moves if x[0] == 'add'), sum(1 for x in moves if x[0] == 'chain'),
        sum(1 for x in moves if x[0] == 'ring')))
    rep = [(kind, p, B) for kind, p, B in moves if one_absorber(B)]
    print('   moves after which the bases have a one-absorber completion:', len(rep))
    for kind, p, B in rep[:5]:
        print('     ', kind, p, B)
    freerep = [(kind, p) for kind, p, B in moves if free(B)]
    print('   moves after which the bases have a free completion (OC):', len(freerep), freerep[:5])
    # context: EFX0 existence and domination (brute force over all n^m allocations is too many for n = 6, m = 10;
    # restrict to allocations of relevant goods by giving every good only to agents valuing it or to anyone if none)
    if not rep:
        print('OC1 FAILS for this order (independent replay)')
    return not rep


if __name__ == '__main__':
    if len(sys.argv) > 1:
        ds = json.load(open(sys.argv[1]))
        idx = int(sys.argv[2]) if len(sys.argv) > 2 else 0
        sys.exit(0 if main(ds[idx]) else 1)
    sys.exit(0 if main(DEFAULT) else 1)
