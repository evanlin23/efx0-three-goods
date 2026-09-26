#!/usr/bin/env python3
"""Plain brute-force referee for conjecture C4min (k4/c4x.md §5) on one strict profile, written from the definitions
of k4/c4x.md §1 for k4/c4min_hunt.md; it shares no code with k4/c4x.c, k4/c4x_check.py or k4/c4min_hunt.c.

Profile: agents i with relevant goods R_i (3 or 4 goods) and integer values v_i (strict: all nonempty subset sums of
R_i distinct). Every quantity is computed literally:
  - pre-allocations: every tuple (B_1, .., B_n) of pairwise disjoint subsets B_i ⊆ R_i with |B_i| <= 2 (itertools);
  - needs N_i = {g in R_i \\ B_i : v_i(g) > v_i(B_i)}; valid iff every good of NA = ∪ N_i is the whole base of some
    agent; frozen agents: one-good base in NA; cap = 0 (frozen) or 2 - |B_i|;
  - deficit: |J| - S if <= 0; else min over free owners o and all C ⊆ J (no pruning) such that for every j != o and
    every h in X_o = B_o ∪ (J \\ C): v_j(X_o \\ h) <= v_j(B_j), of |C| - S_o(C), with S_o(C) from the owner's needs
    {g in R_o \\ X_o : v_o(g) > v_o(X_o)} (base=True: from B_o);
  - completable: some owner o (free) or none, and some map of the junk goods to agents (each junk good to one agent)
    such that frozen non-owners get nothing, free non-owners end with <= 2 goods, and (OC4) holds literally; every
    completion found is also checked to be EFX0 by the raw definition (v_i(X_i) >= v_i(X_j \\ h) for all i != j,
    h in X_j) with at most one bundle of more than two goods;
  - K4.D: every allocation of the m goods to the n agents (n^m), raw EFX0 and at most one bundle of > 2 goods.
Usage (library): brute(sets, vals, m) -> dict with fstar, dstar, valid, minfrozen, good, completable;
                 k4d(sets, vals, m) -> an EFX0 D2 allocation or None.
Command line: c4min_brute.py JSON  where JSON = {"m": m, "sets": [[..]..], "vals": [[..]..]} (vals in the order of
sets); prints the result."""
import itertools, json, sys

INF = 10 ** 6


def value(vi, S):
    return sum(vi.get(g, 0) for g in S)


def base_options(R):
    return [frozenset(c) for k in range(3) for c in itertools.combinations(R, k)]


def needs(vi, R, B):
    vb = value(vi, B)
    return frozenset(g for g in R if g not in B and vi[g] > vb)


def threatened(vj, X, Bj):
    """max over h in X of v_j(X \\ h) > v_j(B_j), literally"""
    return any(value(vj, X - {h}) > value(vj, Bj) for h in X)


def preallocations(sets, vals, m):
    n = len(sets)
    opts = [base_options(S) for S in sets]
    for bases in itertools.product(*opts):
        used = set()
        ok = True
        for B in bases:
            if used & B: ok = False; break
            used |= B
        if not ok: continue
        N = [needs(vals[i], sets[i], bases[i]) for i in range(n)]
        NA = frozenset().union(*N)
        singles = {next(iter(B)) for B in bases if len(B) == 1}
        if not NA <= singles: continue
        yield bases, N, NA, frozenset(range(m)) - used


def frozen_set(bases, NA):
    return [len(B) == 1 and B <= NA for B in bases]


def deficit(sets, vals, bases, N, NA, J, base=False):
    n = len(sets)
    fz = frozen_set(bases, NA)
    cap = [0 if fz[i] else 2 - len(bases[i]) for i in range(n)]
    S = sum(cap)
    if len(J) - S <= 0: return len(J) - S
    best = INF
    Jl = sorted(J)
    for o in range(n):
        if fz[o]: continue
        for k in range(len(Jl) + 1):
            for C in itertools.combinations(Jl, k):
                C = frozenset(C)
                X = bases[o] | (J - C)
                if any(threatened(vals[j], X, bases[j]) for j in range(n) if j != o): continue
                if base:
                    NAp = NA
                else:
                    vx = value(vals[o], X)
                    No = frozenset(g for g in sets[o] if g not in X and vals[o][g] > vx)
                    NAp = frozenset().union(*[N[j] for j in range(n) if j != o]) | No
                So = sum(0 if (len(bases[j]) == 1 and bases[j] <= NAp) else 2 - len(bases[j]) for j in range(n) if j != o)
                best = min(best, len(C) - So)
    return best


def raw_efx0_d2(sets, vals, X):
    n = len(X)
    if sum(len(x) > 2 for x in X) > 1: return False
    for i in range(n):
        for j in range(n):
            if i == j: continue
            for h in X[j]:
                if value(vals[i], X[i]) < value(vals[i], X[j] - {h}): return False
    return True


def completable(sets, vals, bases, N, NA, J, base=False):
    """some completion (owner or none) with (OC4); returns the allocation or None"""
    n = len(sets)
    fz = frozen_set(bases, NA)
    Jl = sorted(J)
    owners = [None] + [o for o in range(n) if not fz[o]]
    for o in owners:
        for owners_of_junk in itertools.product(range(n), repeat=len(Jl)):
            X = [set(B) for B in bases]
            for g, a in zip(Jl, owners_of_junk): X[a].add(g)
            X = [frozenset(x) for x in X]
            if o is None:
                NAp = NA
            elif base:
                NAp = NA
            else:
                vx = value(vals[o], X[o])
                No = frozenset(g for g in sets[o] if g not in X[o] and vals[o][g] > vx)
                NAp = frozenset().union(*[N[j] for j in range(n) if j != o]) | No
            ok = True
            for j in range(n):
                if j == o: continue
                fzj = len(bases[j]) == 1 and bases[j] <= NAp
                if fzj and X[j] != bases[j]: ok = False; break
                if not fzj and len(X[j]) > 2: ok = False; break
            if not ok: continue
            if o is not None:
                if any(value(vals[j], X[o] - {h}) > value(vals[j], X[j]) for j in range(n) if j != o for h in X[o]): continue
            assert raw_efx0_d2(sets, vals, X), ('completion is not EFX0-D2', bases, o, X)
            return X
    return None


def brute(sets, vals, m, base=False, want_completable=True):
    Ps = list(preallocations(sets, vals, m))
    fstar = min(len(NA) for _, _, NA, _ in Ps)
    mins = [P for P in Ps if len(P[2]) == fstar]
    defs = [deficit(sets, vals, *P, base=base) for P in mins]
    res = {'fstar': fstar, 'dstar': min(defs), 'valid': len(Ps), 'minfrozen': len(mins),
           'good': sum(d <= 0 for d in defs), 'sigma': 2 * len(sets) - m}
    if want_completable:
        comp = 0
        for P, dd in zip(mins, defs):
            if dd <= 0 or completable(sets, vals, *P, base=base) is not None: comp = 1; break
        res['completable'] = comp
    return res


def verify_certificate(sets, vals, m, bases, owner, C, base=False):
    """Check a C4min certificate literally: bases (list of sets) form a valid pre-allocation with f frozen agents,
    and owner (None: no owner) with C ⊆ J is a removal-only completion: |J| <= S if owner is None; otherwise the
    owner is free, X_o = B_o ∪ (J \ C) threatens nobody holding its base, and |C| <= S_o(C). The completion that puts
    C into the slots (in index order) is built and checked EFX0 (raw definition) with at most one bundle > 2 goods.
    Returns f (the frozen count); the caller must know f* >= f (e.g. f = 0) or f <= sigma for C4min."""
    n = len(sets)
    bases = [frozenset(B) for B in bases]
    used = set()
    for i, B in enumerate(bases):
        assert B <= set(sets[i]) and len(B) <= 2 and not (used & B), ('bad base', i, B)
        used |= B
    N = [needs(vals[i], sets[i], bases[i]) for i in range(n)]
    NA = frozenset().union(*N)
    singles = {next(iter(B)) for B in bases if len(B) == 1}
    assert NA <= singles, 'invalid pre-allocation'
    J = frozenset(range(m)) - used
    fz = frozen_set(bases, NA)
    f = sum(fz)
    X = [set(B) for B in bases]
    if owner is None:
        cap = [0 if fz[i] else 2 - len(bases[i]) for i in range(n)]
        assert len(J) <= sum(cap), 'no owner but |J| > S'
        pool, NAp = sorted(J), NA
    else:
        C = frozenset(C)
        assert C <= J and not fz[owner], 'bad owner or C'
        Xo = bases[owner] | (J - C)
        for j in range(n):
            if j != owner: assert not threatened(vals[j], Xo, bases[j]), ('threat', j)
        if base: NAp = NA
        else:
            vx = value(vals[owner], Xo)
            No = frozenset(g for g in sets[owner] if g not in Xo and vals[owner][g] > vx)
            NAp = frozenset().union(*[N[j] for j in range(n) if j != owner]) | No
        cap = [0 if (j == owner or (len(bases[j]) == 1 and bases[j] <= NAp)) else 2 - len(bases[j]) for j in range(n)]
        assert len(C) <= sum(cap), ('|C| > S_o(C)', len(C), sum(cap))
        X[owner] |= Xo
        pool = sorted(C)
    for j in range(n):
        while pool and len(X[j]) < len(bases[j]) + cap[j]: X[j].add(pool.pop())
    assert not pool
    assert raw_efx0_d2(sets, vals, [frozenset(x) for x in X]), 'completion not EFX0-D2'
    return f


def k4d(sets, vals, m):
    n = len(sets)
    for own in itertools.product(range(n), repeat=m):
        X = [frozenset(g for g in range(m) if own[g] == i) for i in range(n)]
        if raw_efx0_d2(sets, vals, X): return X
    return None


def main():
    inst = json.loads(sys.argv[1]) if len(sys.argv) > 1 else json.load(sys.stdin)
    sets, m = inst['sets'], inst['m']
    vals = [dict(zip(S, v)) for S, v in zip(sets, inst['vals'])]
    r = brute(sets, vals, m, base=inst.get('base', False))
    print(json.dumps(r))
    if inst.get('k4d'):
        print('K4.D allocation:', k4d(sets, vals, m))


if __name__ == '__main__':
    main()
