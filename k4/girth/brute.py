"""Brute force over partial orientations (k4/girth.md, section 4).  Written from the raw definitions; shares only the
Inst class with lss.py.

A partial orientation gives each good to one of its valuers or leaves it unallocated (goods nobody values stay
unallocated).  It is EFX0 if no agent strongly envies another bundle (raw definition, all goods counted).

    pareto_max(I)          the Pareto-maximal value vectors among partial EFX0 orientations, with their orientations
    completable(I, X)      can the unallocated goods be added to bundles so that the complete allocation is EFX0?
    check_PL(I)            Conjecture PL: every Pareto-maximal partial EFX0 orientation is completable
"""
import itertools

from lss import Inst, is_efx0


def orientations(I):
    choices = [[-1] + sorted(I.edge[g]) for g in range(I.m)]
    for assign in itertools.product(*choices):
        X = [set() for _ in range(I.n)]
        for g, a in enumerate(assign):
            if a >= 0:
                X[a].add(g)
        yield assign, X


def efx0_partial(I, X):
    for i in range(I.n):
        vi = I.val(i, X[i])
        for j in range(I.n):
            if j != i and X[j] and vi < I.threat(i, X[j]):
                return False
    return True


def pareto_max(I):
    best = {}                                     # value vector -> list of assignments
    for assign, X in orientations(I):
        if not efx0_partial(I, X):
            continue
        vec = tuple(I.val(i, X[i]) for i in range(I.n))
        best.setdefault(vec, []).append(assign)
    vecs = list(best)
    out = []
    for v in vecs:
        if any(w != v and all(a >= b for a, b in zip(w, v)) for w in vecs):
            continue
        out.append((v, best[v]))
    return out


def completable(I, assign):
    U = [g for g, a in enumerate(assign) if a < 0]
    base = [set() for _ in range(I.n)]
    for g, a in enumerate(assign):
        if a >= 0:
            base[a].add(g)
    for extra in itertools.product(range(I.n), repeat=len(U)):
        X = [set(b) for b in base]
        for g, a in zip(U, extra):
            X[a].add(g)
        if is_efx0(I, X):
            return X
    return None


def check_PL(I, every=True):
    """every=True: every Pareto-max orientation completable; returns (ok, counterexample assign or None)"""
    pm = pareto_max(I)
    for vec, assigns in pm:
        for a in assigns:
            if completable(I, a) is None:
                return False, (vec, a)
    return True, None


def bundles_of(I, assign):
    X = [set() for _ in range(I.n)]
    for g, a in enumerate(assign):
        if a >= 0:
            X[a].add(g)
    return X


def safe_sets(I, X, U):
    """S_i = non-envied u with v_i(X_u + U_i) <= v_i(X_i), for envied i (k4/girth.md, Lemma PARK)"""
    from lss import envied
    env = [i for i in range(I.n) if envied(I, X, i)]
    S = {}
    for i in env:
        Ui = U & I.R[i]
        S[i] = {u for u in range(I.n) if u not in env and I.val(i, X[u] | Ui) <= I.val(i, X[i])}
    return env, S


def park_condition(I, assign):
    """(a) every unallocated good valued by someone has only envied valuers... no: the PARK hypothesis of
    k4/girth.md section 3: every unallocated edge whose valuers are all envied has a common safe vertex, and every
    other unallocated edge has a non-envied valuer.  Returns (holds, clean_sink_exists)."""
    from lss import envied
    X = bundles_of(I, assign)
    U = {g for g, a in enumerate(assign) if a < 0}
    env, S = safe_sets(I, X, U)
    ok = True
    for e in U:
        val = I.edge[e]
        if not val:
            continue
        if any(j not in env for j in val):
            continue
        common = set(range(I.n))
        for i in val:
            common &= S[i]
        if not common:
            ok = False
    clean = [s for s in range(I.n) if s not in env and not any(X[s] & I.R[i] for i in env)]
    return ok, bool(clean)


def park_slack(I, assign):
    """Completion by PARK sinks plus slack absorbers (k4/girth.md, section 4): every leftover good whose valuers are
    all envied goes either to a common safe vertex, or alone to a non-envied u with |X_u| = 1 that takes nothing else.
    Goods with a non-envied valuer are oriented to it first (Lemma PARK, step 1).  Exhaustive over the choices;
    returns the completed allocation or None.  Linear hypergraphs only (that is where the rule is proved sound);
    the result is re-checked with the raw EFX0 definition."""
    from lss import envied
    X = bundles_of(I, assign)
    U = {g for g, a in enumerate(assign) if a < 0}
    env, S = safe_sets(I, X, U)
    N = [u for u in range(I.n) if u not in env]
    Y = [set(b) for b in X]
    L = []
    for e in sorted(U):
        nb = [j for j in I.edge[e] if j not in env]
        if nb:
            Y[nb[0]].add(e)
        elif I.edge[e]:
            L.append(e)
        else:
            Y[N[0] if N else 0].add(e)                 # valued by nobody (excluded by L3 anyway)
    opts = []
    for e in L:
        common = set(N)
        for i in I.edge[e]:
            common &= S[i]
        o = [('park', u) for u in sorted(common)] + [('slack', u) for u in N if len(X[u]) == 1]
        opts.append(o)
    for choice in itertools.product(*opts):
        slack = [u for k, u in choice if k == 'slack']
        park = {u for k, u in choice if k == 'park'}
        if len(set(slack)) < len(slack) or set(slack) & park:
            continue
        Z = [set(b) for b in Y]
        for e, (k, u) in zip(L, choice):
            Z[u].add(e)
        if any(k == 'slack' and Z[u] != X[u] | {e} for e, (k, u) in zip(L, choice)):
            continue
        from lss import is_efx0
        if is_efx0(I, Z):
            return Z
    return None
