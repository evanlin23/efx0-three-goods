"""Replay the failed forms of the insertion lemma (k4/induct.md; attempts/k4-induct-*.md).

Every claim is re-derived here by brute force with k4/induct_bf.py (itertools over all allocations, raw EFX0), which
shares no code with k4/induct.c (the tool that found the examples). Each instance is a strict k = 4 core profile:
SETS[i] lists agent i's goods, PROF[i] its integer values on them (a representative of its strict balanced type).

Notation: E(J) = EFX0 allocations of J. For w with 4 goods and d in R_w:
  G-form: X' in E(I - d) (d deleted); r(X') = min over X in E(I) of #{g != d : X(g) != X'(g)}.
  B-form: X' in E(I - w - d) (agent w and d deleted); r(X') = min over X in E(I) of #{g != d : X(g) != X'(g)}.
  V-form: Y in E(I_wd) (w's value of d set to 0); r(Y) = min over X in E(I) of #{g : X(g) != Y(g)}.
Usage: python3 attempts/k4_induct_attempts.py [NAME ...]   (default: all)
"""
import os, sys, math
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'k4'))
from induct_bf import valuation, all_efx0, enviers, placements, bundles, efx0


def inst(sets, prof):
    m = 1 + max(g for S in sets for g in S)
    return valuation(sets, prof, m), m


def dist(X, Y, skip=()):
    return sum(1 for g in X if g not in skip and X[g] != Y.get(g))


def r_values(V, m, n, form, w, d):
    """list of (X', r(X')) over every X' of the smaller instance."""
    A = list(range(n)); EI = all_efx0(V, list(range(m)), A)
    if form == 'G':
        Es = all_efx0(V, [g for g in range(m) if g != d], A)
        return [(X, min(dist(X, Y, {d}) for Y in EI)) for X in Es]
    if form == 'B':
        Es = all_efx0(V, [g for g in range(m) if g != d], [a for a in A if a != w])
        return [(X, min(dist(X, Y, {d}) for Y in EI)) for X in Es]
    if form == 'V':
        V2 = [row[:] for row in V]; V2[w][d] = 0
        Es = all_efx0(V2, list(range(m)), A)
        return [(X, min(dist(X, Y) for Y in EI)) for X in Es]


def four_good(sets):
    return [w for w, S in enumerate(sets) if len(S) == 4]


def check_forall(name, sets, prof, form, bound):
    """Claim: for EVERY 4-good w and d in R_w, some X' of the smaller instance has r(X') > bound."""
    V, m = inst(sets, prof); n = len(sets)
    worst = {}
    for w in four_good(sets):
        for d in sets[w]:
            worst[(w, d)] = max(r for _, r in r_values(V, m, n, form, w, d))
    ok = all(x > bound for x in worst.values())
    print(f'[{name}] {form}-form, every X\' within repair {bound}: fails for every (w, d)? {ok}; '
          f'max over X\' of r per (w, d): {worst}')
    return ok


POT = {
    'max v_w': lambda V, X, w, A: sum(V[w][g] for g in X if X[g] == w),
    'min v_w': lambda V, X, w, A: -sum(V[w][g] for g in X if X[g] == w),
    'min #enviers(w)': lambda V, X, w, A: -len(enviers(V, X, w, A)),
    '(min #enviers(w), max v_w)': lambda V, X, w, A: (-len(enviers(V, X, w, A)), sum(V[w][g] for g in X if X[g] == w)),
    'max utilitarian': lambda V, X, w, A: sum(V[a][g] for g in X for a in [X[g]]),
    'max Nash welfare': lambda V, X, w, A: nash(V, X, A),
    '(min #enviers(w), max utilitarian)': lambda V, X, w, A: (-len(enviers(V, X, w, A)), sum(V[a][g] for g in X for a in [X[g]])),
    'min #agents that envy someone': lambda V, X, w, A: -sum(1 for i in A if any(
        sum(V[i][g] for g in X if X[g] == j) > sum(V[i][g] for g in X if X[g] == i) for j in A if j != i)),
}


def nash(V, X, A):
    vals = [sum(V[i][g] for g in X if X[g] == i) for i in A]
    return (sum(1 for x in vals if x > 0), sum(math.log(x) for x in vals if x > 0))


def check_potential(name, sets, prof, pot):
    """Claim: for EVERY 4-good w and d in R_w, some maximizer X' of the potential over E(I - d) has no placement
    of d that keeps EFX0 (r(X') >= 1)."""
    V, m = inst(sets, prof); n = len(sets); A = list(range(n))
    res = {}; some = {}
    for w in four_good(sets):
        for d in sets[w]:
            Es = all_efx0(V, [g for g in range(m) if g != d], A)
            vals = [POT[pot](V, X, w, A) for X in Es]
            best = max(vals)
            res[(w, d)] = any(v == best and not placements(V, X, d, A) for v, X in zip(vals, Es))
            some[(w, d)] = any(v == best and placements(V, X, d, A) for v, X in zip(vals, Es))
    ok = all(res.values())
    print(f'[{name}] potential "{pot}": some maximizer of E(I - d) admits no placement of d, for every (w, d)? {ok}'
          f'   (weaker, some-maximizer form also fails here, i.e. no (w, d) has a maximizer admitting a placement: '
          f'{not any(some.values())})')
    return ok


def check_potential_V(name, sets, prof, pot):
    """V-form: Claim: for EVERY 4-good w and d in R_w, some maximizer Y of the potential over E(I_wd) (w's value of d
    set to 0; the potential evaluated with I_wd's values) is not EFX0 for I."""
    V, m = inst(sets, prof); n = len(sets); A = list(range(n))
    res = {}
    for w in four_good(sets):
        for d in sets[w]:
            V2 = [row[:] for row in V]; V2[w][d] = 0
            Es = all_efx0(V2, list(range(m)), A)
            vals = [POT[pot](V2, X, w, A) for X in Es]
            best = max(vals)
            res[(w, d)] = any(v == best and not efx0(V, X, A) for v, X in zip(vals, Es))
    ok = all(res.values())
    print(f'[{name}] V-form, potential "{pot}": some maximizer is not EFX0 for I, for every (w, d)? {ok}')
    return ok


def check_q4_rules(name, sets, prof):
    """Claim: for every 4-good w, d in R_w and agent h, some X' in E(I - d) minimizing #enviers(h) has d -> h not EFX0.
    (The rules 'select by PS for h, then give d to h'.) Also: every 4-good agent has no private good."""
    V, m = inst(sets, prof); n = len(sets); A = list(range(n))
    deg = [sum(g in S for S in sets) for g in range(m)]
    allq4 = all(all(deg[g] >= 2 for g in sets[w]) for w in four_good(sets))
    fails = True; some = []; tot = 0
    for w in four_good(sets):
        for d in sets[w]:
            Es = all_efx0(V, [g for g in range(m) if g != d], A)
            for h in A:
                env = [len(enviers(V, X, h, A)) for X in Es]
                mn = min(env); tot += 1
                adm = [h in placements(V, X, d, A) for e, X in zip(env, Es) if e == mn]
                if all(adm): fails = False
                if any(adm): some.append((w, d, h))
    print(f'[{name}] every 4-good agent is Q4: {allq4}; no rule (w, d, h) works: {fails}')
    print(f'[{name}]   (existence form, not a claim of failure: {len(some)} of {tot} triples (w, d, h) have SOME minimizer '
          f'admitting d -> h: {some})')
    return fails and allq4


def check_ps_private(name, sets, prof):
    """Positive control: for each 4-good w with a private good p, some X' in E(I - p) leaves w unenvied, and then
    X' + (p -> w) is EFX0 (Lemma 2)."""
    V, m = inst(sets, prof); n = len(sets); A = list(range(n))
    deg = [sum(g in S for S in sets) for g in range(m)]
    ok = True
    for w in four_good(sets):
        for p in sets[w]:
            if deg[p] != 1: continue
            Es = all_efx0(V, [g for g in range(m) if g != p], A)
            good = [X for X in Es if not enviers(V, X, w, A)]
            ok &= bool(good) and all(w in placements(V, X, p, A) for X in good) and \
                all(w not in placements(V, X, p, A) for X in Es if enviers(V, X, w, A))
    print(f'[{name}] PS(I - p, w) holds and d -> w works exactly on the X\' with w unenvied: {ok}')
    return ok


CASES = {
    # G-form, every X', bounded repair
    'G-r0': lambda: check_forall('G-r0', [[0, 1, 2, 3], [1, 2, 3]], [[2, 3, 8, 4], [2, 4, 3]], 'G', 0),
    'G-r1': lambda: check_forall('G-r1', [[0, 2, 3, 4], [1, 2, 3, 4]], [[4, 10, 8, 3], [4, 8, 10, 3]], 'G', 1),
    'G-r2': lambda: check_forall('G-r2', [[0, 1, 3, 4], [2, 3, 4], [2, 3, 4]], [[5, 3, 7, 6], [2, 3, 4], [2, 3, 4]], 'G', 2),
    'G-r3': lambda: check_forall('G-r3', [[0, 3, 4, 5], [1, 4, 5], [2, 4, 5], [3, 4, 5], [3, 4, 5]],
                                 [[10, 4, 3, 8], [4, 2, 3], [2, 3, 4], [3, 4, 2], [4, 3, 2]], 'G', 3),
    # B-form (remove agent w and d), every X'
    'B-r0': lambda: check_forall('B-r0', [[0, 1, 2, 3], [1, 2, 3]], [[4, 8, 6, 1], [4, 2, 3]], 'B', 0),
    'B-r1': lambda: check_forall('B-r1', [[0, 1, 3, 4], [2, 3, 4], [2, 3, 4]], [[3, 6, 10, 8], [4, 3, 2], [4, 2, 3]], 'B', 1),
    'B-r2': lambda: check_forall('B-r2', [[0, 2, 3, 5], [1, 4, 6], [2, 3, 6], [4, 5, 6]], [[4, 7, 2, 8], [3, 2, 4], [3, 2, 4], [2, 3, 4]], 'B', 2),
    # V-form (w stops valuing d), every Y
    'V-r0': lambda: check_forall('V-r0', [[0, 1, 3, 4], [2, 3, 4]], [[4, 3, 8, 2], [4, 3, 2]], 'V', 0),
    'V-r1': lambda: check_forall('V-r1', [[0, 2, 3, 4], [1, 3, 4], [2, 3, 4]], [[3, 6, 8, 4], [3, 4, 2], [4, 3, 2]], 'V', 1),
    'V-r3': lambda: check_forall('V-r3', [[0, 2, 4, 5], [1, 3, 5], [3, 4, 5]], [[3, 6, 2, 10], [3, 4, 2], [3, 2, 4]], 'V', 3),
    # extremal X' (G-form): smallest failures per potential
    'pot-maxvw': lambda: check_potential('pot-maxvw', [[0, 1, 2, 3], [1, 2, 3], [1, 2, 3]], [[8, 4, 7, 2], [4, 3, 2], [3, 2, 4]], 'max v_w'),
    'pot-minvw': lambda: check_potential('pot-minvw', [[0, 1, 2, 3], [1, 2, 3]], [[4, 8, 6, 1], [4, 2, 3]], 'min v_w'),
    'pot-env': lambda: check_potential('pot-env', [[0, 3, 4], [1, 2, 3, 4], [1, 2, 4]], [[2, 3, 4], [3, 2, 8, 4], [2, 3, 4]], 'min #enviers(w)'),
    'pot-env-vw': lambda: check_potential('pot-env-vw', [[0, 3, 4], [1, 2, 3, 4], [1, 2, 4]], [[2, 4, 3], [4, 2, 10, 7], [2, 3, 4]], '(min #enviers(w), max v_w)'),
    'pot-util': lambda: check_potential('pot-util', [[0, 2, 4, 5], [1, 4, 5], [3, 4, 5]], [[3, 6, 4, 8], [2, 4, 3], [2, 4, 3]], 'max utilitarian'),
    'pot-nash': lambda: check_potential('pot-nash', [[0, 2, 4, 5], [1, 4, 5], [3, 4, 5]], [[4, 3, 6, 8], [2, 3, 4], [3, 4, 2]], 'max Nash welfare'),
    'pot-env-util': lambda: check_potential('pot-env-util', [[0, 3, 4], [1, 2, 3, 4], [1, 2, 4]], [[2, 4, 3], [4, 2, 10, 7], [2, 3, 4]], '(min #enviers(w), max utilitarian)'),
    'pot-envy': lambda: check_potential('pot-envy', [[0, 1, 2, 3], [1, 2, 3], [1, 2, 3]], [[2, 8, 5, 4], [4, 2, 3], [4, 3, 2]], 'min #agents that envy someone'),
    # extremal Y in the V-form
    'V-pot-env-util': lambda: check_potential_V('V-pot-env-util', [[0, 2, 3, 4], [1, 2, 3, 4]], [[8, 4, 3, 2], [8, 4, 3, 2]],
                                               '(min #enviers(w), max utilitarian)'),
    # Q4: PS-selected placements
    'q4-rules': lambda: check_q4_rules('q4-rules', [[0, 3, 4], [1, 2, 3, 4], [1, 2, 4]], [[2, 4, 3], [6, 4, 8, 3], [2, 3, 4]]),
    # positive control (not a failure): the private-good step on the G-r1 and G-r3 instances
    'ctrl-private': lambda: check_ps_private('ctrl-private', [[0, 2, 3, 4], [1, 2, 3, 4]], [[4, 10, 8, 3], [4, 8, 10, 3]]) and
                            check_ps_private('ctrl-private', [[0, 3, 4, 5], [1, 4, 5], [2, 4, 5], [3, 4, 5], [3, 4, 5]],
                                             [[10, 4, 3, 8], [4, 2, 3], [2, 3, 4], [3, 4, 2], [4, 3, 2]]),
}


def main():
    names = sys.argv[1:] or list(CASES)
    bad = [nm for nm in names if not CASES[nm]()]
    print('ALL CLAIMS CONFIRMED' if not bad else f'NOT CONFIRMED: {bad}')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
