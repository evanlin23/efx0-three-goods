#!/usr/bin/env python3
"""Referee spot check of Theorem N2's type reduction (k4/haxell.md §6 on claude/k4-haxell at 158b4d9): Lemma TD
(type-determinedness), Lemma OR (orbit reduction, by counting the canonical classes), and the theorem itself on
random strict instances. Own code; nothing from k4/haxell/ is run or imported.

  count : canonical classes over all n = 2 shapes (a A-only, s shared, b B-only goods; 1 <= a+s, s+b <= 4), with
          t(d) strict labeled types on d goods (1, 1, 2, 12, 336 for d = 0..4, K4.OT): t(a+s)/(a! s!) * t(s+b)/b!.
  td    : pairs of valuations v, w with the same strict type per agent (bucketed by the signs of all comparisons of
          disjoint nonempty subsets): partial EFX0 of every partial allocation, and the improvement relation
          v_i(Y_i) > v_i(X_i) on sampled pairs, agree. Control: w with a different type for one agent.
  n2    : random strict n = 2 instances (every good valued, 1 <= |R_i| <= 4, m <= 6): at every partial EFX0 state
          with a nonempty pool, some composite of <= 2 moves (set transfer from a holder or the pool to an agent;
          swap of two goods with different holders, the pool counting as a holder; trade of the two bundles) reaches
          a partial EFX0 state with a smaller pool, or one swap of an A-good with a B-good makes both agents strictly
          better and stays partial EFX0.
"""
import itertools, random, sys, json
from math import factorial
from collections import Counter

def count_classes():
    t = {0: 1, 1: 1, 2: 2, 3: 12, 4: 336}
    tot = shapes = 0
    for a in range(5):
        for s in range(5):
            for b in range(5):
                if 1 <= a + s <= 4 and 1 <= s + b <= 4:
                    shapes += 1
                    tot += t[a + s] // (factorial(a) * factorial(s)) * (t[s + b] // factorial(b))
    return shapes, tot

def subsets(S):
    S = list(S)
    for r in range(len(S) + 1):
        yield from itertools.combinations(S, r)

def signature(vals):
    """signs of v(S) - v(T) over ordered pairs of disjoint nonempty subsets of range(d); None if some equality."""
    d = len(vals); sig = []
    for S in subsets(range(d)):
        if not S:
            continue
        rest = [g for g in range(d) if g not in S]
        for T in subsets(rest):
            if not T:
                continue
            x = sum(vals[g] for g in S) - sum(vals[g] for g in T)
            if x == 0:
                return None
            sig.append(x > 0)
    return tuple(sig)

def holders_states(m):
    return itertools.product((-1, 0, 1), repeat=m)

def bval(v, i, X, j, skip=None):
    return sum(v[i][g] for g in range(len(X)) if X[g] == j and g != skip)

def pefx0(v, X):
    for i in (0, 1):
        j = 1 - i; own = bval(v, i, X, i)
        for g in range(len(X)):
            if X[g] == j and bval(v, i, X, j, skip=g) > own:
                return False
    return True

def moves(X):
    m = len(X); out = []
    for h in (-1, 0, 1):
        G = [g for g in range(m) if X[g] == h]
        for S in subsets(G):
            if not S:
                continue
            for b in (0, 1):
                if b != h:
                    Y = list(X)
                    for g in S:
                        Y[g] = b
                    out.append(tuple(Y))
    for g, h in itertools.combinations(range(m), 2):
        if X[g] != X[h]:
            Y = list(X); Y[g], Y[h] = X[h], X[g]; out.append(tuple(Y))
    out.append(tuple({-1: -1, 0: 1, 1: 0}[x] for x in X))
    return out

def pool(X):
    return sum(1 for x in X if x == -1)

def n2_ok(v, X):
    p = pool(X)
    one = moves(X)
    for Y in one:
        if pool(Y) < p and pefx0(v, Y):
            return "one"
    for Y in one:
        for Z in moves(Y):
            if pool(Z) < p and pefx0(v, Z):
                return "two"
    m = len(X)
    for g in range(m):
        for h in range(m):
            if X[g] == 0 and X[h] == 1:
                Y = list(X); Y[g], Y[h] = 1, 0; Y = tuple(Y)
                if pefx0(v, Y) and bval(v, 0, Y, 0) > bval(v, 0, X, 0) and bval(v, 1, Y, 1) > bval(v, 1, X, 1):
                    return "pareto_swap"
    return None

def rand_instance(rng, m):
    while True:
        RA = set(rng.sample(range(m), rng.randint(1, min(4, m))))
        rest = set(range(m)) - RA
        if len(rest) > 4:
            continue
        extra = rng.sample(sorted(RA), rng.randint(0, min(len(RA), 4 - len(rest))))
        RB = rest | set(extra)
        if not RB:
            continue
        v = [[0] * m, [0] * m]
        for i, R in ((0, RA), (1, RB)):
            R = sorted(R)
            while True:
                xs = [rng.randint(1, 1000) for _ in R]
                if signature(xs) is not None:
                    break
            for g, x in zip(R, xs):
                v[i][g] = x
        return v

def run_n2(N, seed, mmax):
    rng = random.Random(seed); c = Counter()
    for _ in range(N):
        m = rng.randint(2, mmax); v = rand_instance(rng, m)
        c["instances"] += 1
        for X in holders_states(m):
            if pool(X) == 0 or not pefx0(v, X):
                continue
            c["states"] += 1
            r = n2_ok(v, X)
            c["by_" + str(r)] += 1
            if r is None:
                c["FAIL"] += 1
                print("FAIL", v, X)
    print(json.dumps(dict(source=f"Theorem N2 on random strict instances N={N} seed={seed} m<={mmax}", **dict(sorted(c.items())))))

def run_td(N, seed):
    rng = random.Random(seed); c = Counter()
    for d in (1, 2, 3, 4):
        buckets = {}
        for _ in range(20000):
            xs = [rng.randint(1, 60) for _ in range(d)]
            s = signature(xs)
            if s is not None:
                buckets.setdefault(s, []).append(xs)
        c[f"types_seen_d{d}"] = len(buckets)
    for _ in range(N):
        m = rng.randint(2, 6)
        v = rand_instance(rng, m)
        # a second realization of the same strict types: rescale and perturb until the signature matches
        w = [[0] * m, [0] * m]; ctrl = None
        for i in (0, 1):
            R = [g for g in range(m) if v[i][g] > 0]
            sig = signature([v[i][g] for g in R])
            while True:
                xs = [rng.randint(1, 3000) for _ in R]
                if signature(xs) == sig:
                    break
            for g, x in zip(R, xs):
                w[i][g] = x
        # control: a different strict type for agent 0 (if one exists with the same relevant set)
        R0 = [g for g in range(m) if v[0][g] > 0]
        if len(R0) >= 2:
            for _ in range(200):
                xs = [rng.randint(1, 3000) for _ in R0]
                s = signature(xs)
                if s is not None and s != signature([v[0][g] for g in R0]):
                    ctrl = [list(w[0]), list(w[1])]
                    for g, x in zip(R0, xs):
                        ctrl[0][g] = x
                    break
        states = list(holders_states(m))
        mism = sum(pefx0(v, X) != pefx0(w, X) for X in states)
        c["td_partial_allocs"] += len(states); c["td_EFX0_MISMATCH"] += mism
        for _ in range(200):
            X, Y = rng.choice(states), rng.choice(states)
            for i in (0, 1):
                c["td_improvement_pairs"] += 1
                if (bval(v, i, Y, i) > bval(v, i, X, i)) != (bval(w, i, Y, i) > bval(w, i, X, i)):
                    c["td_improvement_MISMATCH"] += 1
        if ctrl is not None:
            c["control_instances"] += 1
            cm = sum(pefx0(v, X) != pefx0(ctrl, X) for X in states)
            cim = 0
            for _ in range(200):
                X, Y = rng.choice(states), rng.choice(states)
                cim += (bval(v, 0, Y, 0) > bval(v, 0, X, 0)) != (bval(ctrl, 0, Y, 0) > bval(ctrl, 0, X, 0))
            c["control_with_some_EFX0_or_improvement_mismatch"] += (cm + cim) > 0
    print(json.dumps(dict(source=f"Lemma TD N={N} seed={seed}", **dict(sorted(c.items())))))

if __name__ == "__main__":
    if sys.argv[1] == "count":
        s, t = count_classes(); print(json.dumps(dict(shapes=s, canonical_classes=t, note_says=45999)))
    elif sys.argv[1] == "td":
        run_td(int(sys.argv[2]), int(sys.argv[3]))
    else:
        run_n2(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
