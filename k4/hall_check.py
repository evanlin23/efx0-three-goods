#!/usr/bin/env python3
"""Independent plain-Python check of single pre-allocations (k4/hall.md), sharing no code with k4/hall.c.

From the definitions of k4/c4x.md §1 (lean/EFX/PreAllocK.lean): bases B_i ⊆ R_i with |B_i| <= 2, pairwise
disjoint; value-based needs N_i = {g in R_i \\ B_i : v_i(g) > v_i(B_i)}; junk J; valid iff every needed good is the
whole base of one agent (frozen). Completable iff some completion (owner o free, or none) satisfies (OC4): frozen
non-owners get nothing, a free non-owner j gets at most 2 - |B_j| junk goods, the owner the rest; the owner's needs
are taken from its bundle (frozen status and slots recomputed); v_j(X_o \\ h) <= v_j(X_j) for all j != o, h in X_o.
Every completion found is re-checked against the raw EFX0 definition (all pairs of agents, all removed goods).

usage: python3 k4/hall_check.py FILE   where FILE holds lines "agent g:v g:v ..." and one line "bases B_0 | B_1 | ...",
       each B_i a comma-separated list of goods (possibly empty). Prints validity, frozen agents, whether the
       pre-allocation is Pareto-maximal among all valid pre-allocations, whether one with fewer frozen agents exists,
       and whether it is completable (and removal-only completable)."""
import itertools, sys

def load(path):
    vals, bases = [], None
    for line in open(path):
        w = line.split()
        if not w or w[0].startswith('#'): continue
        if w[0] == 'agent': vals.append({int(a): int(b) for a, b in (t.split(':') for t in w[1:])})
        elif w[0] == 'bases':
            parts = ' '.join(w[1:]).split('|')
            bases = [frozenset(int(x) for x in p.replace(' ', '').split(',') if x) for p in parts]
    return vals, bases

def v(val, S): return sum(val.get(g, 0) for g in S)

def needs(val, B): return {g for g in val if g not in B and val[g] > v(val, B)}

def analyse(vals, bases, m):
    n = len(vals)
    used = set().union(*bases)
    J = set(range(m)) - used
    NA = set().union(*(needs(vals[i], bases[i]) for i in range(n)))
    single = {next(iter(B)) for B in bases if len(B) == 1}
    valid = NA <= single and all(len(B) <= 2 and B <= set(vals[i]) for i, B in enumerate(bases))
    frozen = [i for i in range(n) if len(bases[i]) == 1 and next(iter(bases[i])) in NA]
    return valid, J, NA, frozen

def all_valid(vals, m):
    n = len(vals)
    opts = [[frozenset(c) for r in range(3) for c in itertools.combinations(sorted(vals[i]), r)] for i in range(n)]
    out = []
    def rec(i, cur, used):
        if i == n:
            ok, J, NA, fr = analyse(vals, cur, m)
            if ok: out.append((list(cur), len(fr)))
            return
        for B in opts[i]:
            if B & used: continue
            cur.append(B); rec(i + 1, cur, used | B); cur.pop()
    rec(0, [], frozenset())
    return out

def efx0(vals, X):
    n = len(X)
    for i in range(n):
        for j in range(n):
            if i == j: continue
            for h in X[j]:
                if v(vals[i], X[i]) < v(vals[i], X[j] - {h}): return False
    return True

def completable(vals, bases, m, removal_only=False):
    n = len(vals)
    ok, J, NA, frozen = analyse(vals, bases, m)
    assert ok
    Jl = sorted(J)
    owners = [None] + [o for o in range(n) if o not in frozen]
    for o in owners:
        for r in range(len(Jl) + 1):
            for K in itertools.combinations(Jl, r):
                K = set(K)
                if o is None and K: continue
                rest = [g for g in Jl if g not in K]
                if o is None: Xo = set()
                else: Xo = set(bases[o]) | K
                # frozen status with the owner's needs from its bundle
                NAo = set()
                for i in range(n):
                    if i == o: NAo |= {g for g in vals[o] if g not in Xo and vals[o][g] > v(vals[o], Xo)}
                    else: NAo |= needs(vals[i], bases[i])
                fr = {i for i in range(n) if i != o and len(bases[i]) == 1 and next(iter(bases[i])) in NAo}
                cap = {i: (0 if i in fr else 2 - len(bases[i])) for i in range(n) if i != o}
                if len(rest) > sum(max(c, 0) for c in cap.values()): continue
                if removal_only and o is not None:
                    if any(max((v(vals[j], Xo - {h}) for h in Xo), default=0) > v(vals[j], bases[j]) for j in range(n) if j != o): continue
                # assign the rest to slots (every assignment; small instances only)
                slots = [i for i in cap for _ in range(max(cap[i], 0))]
                for pick in itertools.permutations(range(len(slots)), len(rest)):
                    X = [set(bases[i]) for i in range(n)]
                    if o is not None: X[o] = set(Xo)
                    for g, s in zip(rest, pick): X[slots[s]].add(g)
                    if o is None and any(len(x) > 2 for x in X): continue
                    if efx0(vals, X): return True, o, X
                    if removal_only: break
    return False, None, None

def main():
    vals, bases = load(sys.argv[1])
    m = 1 + max(g for val in vals for g in val)
    ok, J, NA, frozen = analyse(vals, bases, m)
    print(f'n {len(vals)} m {m} valid {ok} frozen {frozen} junk {sorted(J)} omega {len(J) - sum(2 - len(B) for i, B in enumerate(bases) if i not in frozen)}')
    allP = all_valid(vals, m)
    minF = min(f for _, f in allP)
    lv = [v(vals[i], bases[i]) for i in range(len(vals))]
    dom = [P for P, f in allP if all(v(vals[i], P[i]) >= lv[i] for i in range(len(vals))) and any(v(vals[i], P[i]) > lv[i] for i in range(len(vals)))]
    print(f'valid pre-allocations {len(allP)}, fewest frozen {minF}, Pareto-maximal {not dom}')
    c, o, X = completable(vals, bases, m)
    print(f'completable {c}' + (f' owner {o} allocation {[sorted(x) for x in X]}' if c else ''))
    c2, _, _ = completable(vals, bases, m, removal_only=True)
    print(f'removal-only completable {c2}')

if __name__ == '__main__':
    main()
