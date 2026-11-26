#!/usr/bin/env python3
"""Referee check of Theorem T1 and Lemmas SINK, PARK, SLACK (k4/girth.md §3-§4, branch claude/k4-girth).

Written from the text of LSS (arXiv 2608.03171v1, §2-§3, read via pdftotext) and k4/girth.md; shares no code with
k4/girth/.

Valuations: either additive, or general monotone with LSS's irrelevance (v_i(S) = f_i(S ∩ R_i), f_i a random monotone
normalized set function on the subsets of R_i). The hypergraph: good g is the edge R^{-1}(g) = {i : g ∈ R_i}.

T1: linear hypergraph (two agents share <= 1 good) and vertex 0 on no 3-cycle (Berge). Run LSS Algorithms 1-3 with
random resolutions of every choice (which envied vertex in Alg. 2 line 3, argmax ties, which (e, j) in Alg. 3 line 1);
check Properties (1)-(4) after Algorithm 2 and raw EFX0 + completeness at the end.

PARK / SLACK: enumerate every partial orientation of a small linear instance, keep the EFX0 ones with (3) for all
and (4) for the envied agents, and test the lemmas' conclusions for every allowed choice.
"""
import itertools, random, sys, json, os
BAD0 = os.environ.get('GIRTH_BAD0') == '1'  # mutation: vertex 0 ON a 3-cycle

class Inst:
    def __init__(self, n, R, f):
        self.n = n; self.R = R  # R[i]: frozenset of goods relevant to i
        self.f = f              # f[i]: dict frozenset(subset of R[i]) -> value
        self.m = 1 + max([g for r in R for g in r] + [-1])
    def v(self, i, S):
        return self.f[i][frozenset(S) & self.R[i]]

def additive(n, R, rng, maxv=9):
    f = []
    for i in range(n):
        w = {g: rng.randint(1, maxv) for g in R[i]}
        d = {}
        for k in range(len(R[i]) + 1):
            for c in itertools.combinations(sorted(R[i]), k):
                d[frozenset(c)] = sum(w[g] for g in c)
        f.append(d)
    return f

def monotone(n, R, rng, maxv=9):
    """random monotone normalized f on subsets of R_i (values grow along inclusion by random increments >= 0)."""
    f = []
    for i in range(n):
        items = sorted(R[i]); d = {frozenset(): 0}
        for k in range(1, len(items) + 1):
            for c in itertools.combinations(items, k):
                S = frozenset(c)
                lo = max(d[S - {g}] for g in S)
                d[S] = lo + (rng.randint(0, maxv) if rng.random() < 0.8 else 0)
        f.append(d)
    return f

def edges(inst):
    E = {}
    for g in range(inst.m):
        E[g] = frozenset(i for i in range(inst.n) if g in inst.R[i])
    return E

def linear(inst):
    for i, j in itertools.combinations(range(inst.n), 2):
        if len(inst.R[i] & inst.R[j]) > 1:
            return False
    return True

def on_3cycle(inst, x):
    """Berge 3-cycle through x: distinct vertices x, y, z and distinct goods e1 (x,y), e2 (y,z), e3 (z,x)."""
    n = inst.n; R = inst.R
    for y, z in itertools.permutations([i for i in range(n) if i != x], 2):
        for e1 in R[x] & R[y]:
            for e2 in R[y] & R[z]:
                for e3 in R[z] & R[x]:
                    if len({e1, e2, e3}) == 3:
                        return True
    return False

def efx0(inst, X):
    for i in range(inst.n):
        vi = inst.v(i, X[i])
        for j in range(inst.n):
            if i != j and X[j]:
                for g in X[j]:
                    if inst.v(i, X[j] - {g}) > vi:
                        return False
    return True

def envied(inst, X):
    return {j for j in range(inst.n) if any(inst.v(i, X[j]) > inst.v(i, X[i]) for i in range(inst.n) if i != j)}

def lss(inst, zero, rng):
    """LSS Algorithms 1-3 with vertex `zero` as 0; labels: zero=0, its neighbours 1..n0 (random), others above."""
    n = inst.n; E = edges(inst)
    nb = [i for i in range(n) if i != zero and inst.R[i] & inst.R[zero]]
    rest = [i for i in range(n) if i != zero and i not in nb]
    rng.shuffle(nb); rng.shuffle(rest)
    order = [zero] + nb + rest
    label = {a: k for k, a in enumerate(order)}
    X = [set() for _ in range(n)]
    def U():
        held = set().union(*X)
        return {g for g in range(inst.m) if g not in held}
    def fixprop3():
        while True:
            Ug = U()
            cands = [j for j in range(n) if any(inst.v(j, {e}) > inst.v(j, X[j]) for e in Ug if j in E[e])]
            if not cands:
                return
            j = max(cands, key=lambda a: label[a])
            Uj = [e for e in Ug if j in E[e]]
            best = max(inst.v(j, {e}) for e in Uj)
            e = rng.choice([e for e in Uj if inst.v(j, {e}) == best])
            X[j] = {e}
            if not efx0(inst, X):
                return "fixprop3 broke EFX0"
    r = fixprop3()
    if r:
        return r, X
    while True:
        Ug = U(); Env = envied(inst, X)
        cands = [i for i in Env if inst.v(i, {e for e in Ug if i in E[e]}) > inst.v(i, X[i])]
        if not cands:
            break
        i = rng.choice(cands)
        X[i] = {e for e in Ug if i in E[e]}
        if not efx0(inst, X):
            return "alg2 line 4 broke EFX0", X
        r = fixprop3()
        if r:
            return r, X
    # Properties after Algorithm 2
    Ug = U(); Env = envied(inst, X)
    if not efx0(inst, X) or any(not (j in E[e]) for j in range(n) for e in X[j]):
        return "P1", X
    if zero in Env:
        return "P2 (0 envied)", X
    for i in nb:
        if i in Env and not (X[i] & inst.R[zero]):
            return "P2 (neighbour)", X
    for i in range(n):
        for e in Ug:
            if i in E[e] and inst.v(i, {e}) > inst.v(i, X[i]):
                return "P3", X
    for i in Env:
        if inst.v(i, {e for e in Ug if i in E[e]}) > inst.v(i, X[i]):
            return "P4", X
    # Algorithm 3
    while True:
        Ug = U(); Env = envied(inst, X)
        pairs = [(e, j) for e in Ug for j in E[e] if j not in Env]
        if not pairs:
            break
        e, j = rng.choice(pairs)
        X[j].add(e)
        if not efx0(inst, X):
            return "alg3 line 2 broke EFX0", X
    X[zero] |= U()
    if not efx0(inst, X) or set().union(*X) != set(range(inst.m)):
        return "final not EFX0", X
    return None, X

def rand_linear(rng, n, m, maxsize, maxdeg, tries=200):
    """random hypergraph: each good gets a valuer set of size 0..maxsize; keep linear, degrees <= maxdeg."""
    for _ in range(tries):
        R = [set() for _ in range(n)]
        ok = True
        for g in range(m):
            s = rng.choice([0, 1] + [2] * 3 + list(range(2, maxsize + 1)) * 2)
            cand = [i for i in range(n) if len(R[i]) < maxdeg]
            if len(cand) < s:
                s = len(cand)
            V = rng.sample(cand, s)
            for i in V:
                R[i].add(g)
        R = [frozenset(r) for r in R]
        inst = Inst(n, R, None)
        if linear(inst):
            return R
    return None

def t1_run(N, nlo, nhi, mlo, mhi, maxsize, maxdeg, kind, seed, reps=5):
    rng = random.Random(seed)
    cnt = dict(instances=0, with_3cycle=0, zeros_tested=0, runs=0, fail=0)
    ex = []
    while cnt["instances"] < N:
        n = rng.randint(nlo, nhi); m = rng.randint(mlo, mhi)
        R = rand_linear(rng, n, m, maxsize, maxdeg)
        if R is None:
            continue
        f = additive(n, R, rng) if kind == "add" else monotone(n, R, rng)
        inst = Inst(n, R, f); inst.m = m
        zeros = [x for x in range(n) if (on_3cycle(inst, x) if BAD0 else not on_3cycle(inst, x))]
        if not zeros:
            continue
        cnt["instances"] += 1
        if len(zeros) < n:
            cnt["with_3cycle"] += 1
        for z in zeros:
            cnt["zeros_tested"] += 1
            for _ in range(reps):
                cnt["runs"] += 1
                r, X = lss(inst, z, rng)
                if r:
                    cnt["fail"] += 1
                    if len(ex) < 5:
                        ex.append((r, n, m, [sorted(x) for x in R], z, [sorted(x) for x in X]))
    print(json.dumps(dict(source=f"T1 {kind} N={N} n={nlo}..{nhi} m={mlo}..{mhi} size<={maxsize} deg<={maxdeg} seed={seed}", **cnt)))
    for e in ex:
        print("EXAMPLE", e)

def park_slack_run(N, nlo, nhi, mlo, mhi, maxsize, maxdeg, kind, seed):
    rng = random.Random(seed)
    cnt = dict(instances=0, states=0, park_hyp=0, park_completions=0, park_fail=0, slack_cases=0, slack_fail=0,
               sink_cases=0, sink_fail=0, combo_cases=0, combo_fail=0)
    ex = []
    while cnt["instances"] < N:
        n = rng.randint(nlo, nhi); m = rng.randint(mlo, mhi)
        R = rand_linear(rng, n, m, maxsize, maxdeg)
        if R is None:
            continue
        f = additive(n, R, rng) if kind == "add" else monotone(n, R, rng)
        inst = Inst(n, R, f); inst.m = m; E = edges(inst)
        cnt["instances"] += 1
        opts = [[None] + sorted(E[g]) for g in range(m)]
        for choice in itertools.product(*opts):
            X = [set() for _ in range(n)]
            for g, a in enumerate(choice):
                if a is not None:
                    X[a].add(g)
            if not efx0(inst, X):
                continue
            Ug = {g for g in range(m) if choice[g] is None}
            Env = envied(inst, X); Nn = [i for i in range(n) if i not in Env]
            Ui = [{e for e in Ug if i in E[e]} for i in range(n)]
            if any(inst.v(i, {e}) > inst.v(i, X[i]) for i in range(n) for e in Ui[i]):
                continue  # (3)
            if any(inst.v(i, Ui[i]) > inst.v(i, X[i]) for i in Env):
                continue  # (4) for envied
            cnt["states"] += 1
            S = {i: {u for u in Nn if inst.v(i, X[u] | Ui[i]) <= inst.v(i, X[i])} for i in Env}
            first = [e for e in Ug if E[e] and E[e] <= Env]
            second = [e for e in Ug if E[e] and not E[e] <= Env]
            dead = [e for e in Ug if not E[e]]
            # SINK: for each s with v_i(X_i) >= v_i(X_s ∪ U) for all i != s
            for s in range(n):
                if all(inst.v(i, X[i]) >= inst.v(i, X[s] | Ug) for i in range(n) if i != s):
                    cnt["sink_cases"] += 1
                    Y = [set(x) for x in X]; Y[s] |= Ug
                    if not efx0(inst, Y):
                        cnt["sink_fail"] += 1
            # PARK
            common = {e: set.intersection(*[S[i] for i in E[e]]) for e in first}
            if Nn and all(common[e] for e in first):
                cnt["park_hyp"] += 1
                lists = [sorted(common[e]) for e in first] + [sorted(E[e] - Env) for e in second] + [Nn for e in dead]
                goods = first + second + dead
                allc = list(itertools.product(*lists))
                if len(allc) > 200:
                    allc = rng.sample(allc, 200)
                for pick in allc:
                    cnt["park_completions"] += 1
                    Y = [set(x) for x in X]
                    for e, u in zip(goods, pick):
                        Y[u].add(e)
                    if not efx0(inst, Y):
                        cnt["park_fail"] += 1
                        if len(ex) < 5:
                            ex.append(("park", [sorted(r) for r in R], [sorted(x) for x in X], [sorted(y) for y in Y]))
            # SLACK: u non-envied with X_u = {f}, e unallocated not valued by u
            for u in Nn:
                if len(X[u]) != 1:
                    continue
                for e in Ug:
                    if u in E[e]:
                        continue
                    cnt["slack_cases"] += 1
                    Y = [set(x) for x in X]; Y[u].add(e)
                    if not efx0(inst, Y):
                        cnt["slack_fail"] += 1
                        if len(ex) < 5:
                            ex.append(("slack", [sorted(r) for r in R], [sorted(x) for x in X], u, e))
            # combination (girth.md §3, last paragraph): when every leftover good has only envied valuers,
            # park sinks and distinct one-good non-envied absorbers that take nothing else
            if not second and first:
                abs_ok = [u for u in Nn if len(X[u]) == 1]
                for assign in itertools.product(*[[("p", u) for u in sorted(common[e])] + [("a", u) for u in abs_ok] for e in first]):
                    absorbers = [u for t, u in assign if t == "a"]
                    sinks = {u for t, u in assign if t == "p"}
                    if len(set(absorbers)) != len(absorbers) or (set(absorbers) & sinks):
                        continue
                    cnt["combo_cases"] += 1
                    Y = [set(x) for x in X]
                    for e, (t, u) in zip(first, assign):
                        Y[u].add(e)
                    tgt = [u for u in Nn if u not in absorbers]
                    if dead and not tgt:
                        continue
                    for e in dead:
                        Y[tgt[0]].add(e)
                    if not efx0(inst, Y):
                        cnt["combo_fail"] += 1
                        if len(ex) < 5:
                            ex.append(("combo", [sorted(r) for r in R], [sorted(x) for x in X], assign))
                    if cnt["combo_cases"] % 50 == 0:
                        break
    print(json.dumps(dict(source=f"PARK/SLACK/SINK {kind} N={N} n={nlo}..{nhi} m={mlo}..{mhi} size<={maxsize} deg<={maxdeg} seed={seed}", **cnt)))
    for e in ex:
        print("EXAMPLE", e)

if __name__ == "__main__":
    mode = sys.argv[1]
    a = sys.argv[2:]
    if mode == "t1":
        t1_run(int(a[0]), int(a[1]), int(a[2]), int(a[3]), int(a[4]), int(a[5]), int(a[6]), a[7], int(a[8]))
    elif mode == "park":
        park_slack_run(int(a[0]), int(a[1]), int(a[2]), int(a[3]), int(a[4]), int(a[5]), int(a[6]), a[7], int(a[8]))
