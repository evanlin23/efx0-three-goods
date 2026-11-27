#!/usr/bin/env python3
"""Referee check of Lemma M^c (k4/oc1max_multi.md §9, branch proof/k4-oc1max-multi at 3d157f3). Own code (helpers
from oc1hall_ref.py), raw EFX0; nothing from k4/oc1max_multi/ is run or imported.

States B with (G2): SD picks of random instances (<= 4 relevant goods, n = 3..5), and states one or two random
improving chains away (multi-good bundles that may threaten, frozen singles), kept when (G2) holds. For every owner o
and d = 0, 1:
  brute force: an S^c completion with owner o and d dummy slots exists (o takes the rest; every other agent with <= 1
  base good takes <= 1 junk good; multi-good agents take nothing; <= d junk goods to dummies; raw EFX0);
  formula: some H ⊆ J and F_s ⊆ F_1 (frozen singles other than o) satisfy (C1), (C2), (C3).
Mutations: 'noFs' (only F_s = empty), 'noTauFs' (requirement without the frozen-slot term), 'noComp' (edges without
b_i + v_i(h) >= tau_i).
"""
import itertools, random, sys, json
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from oc1hall_ref import val, threatened, efx0, rel, sd, improving_chains

def classes(v, B):
    n = len(B)
    wanted = {j for j in range(n) if any(i != j and any(v[i][g] > val(v, i, B[i]) for g in B[j]) for i in range(n))}
    N1 = [j for j in range(n) if len(B[j]) <= 1 and j not in wanted]
    F1 = [j for j in range(n) if len(B[j]) == 1 and j in wanted]
    Qm = [j for j in range(n) if len(B[j]) >= 2]
    return N1, F1, Qm

def brute(v, B, o, d):
    n = len(B); m = len(v[0]); J = sorted(set(range(m)) - set().union(*B))
    N1, F1, Qm = classes(v, B)
    recv = [j for j in N1 + F1 if j != o]
    for f in itertools.product(["o", "d"] + recv, repeat=len(J)):
        hs = [a for a in f if a not in ("o", "d")]
        if len(hs) != len(set(hs)) or sum(1 for a in f if a == "d") > d:
            continue
        X = [set(b) for b in B]
        for g, a in zip(J, f):
            if a == "o":
                X[o].add(g)
            elif a != "d":
                X[a].add(g)
        if efx0(v, X):
            return True
    return False

def formula(v, B, o, d, mut=None):
    n = len(B); m = len(v[0]); J = sorted(set(range(m)) - set().union(*B))
    N1, F1, Qm = classes(v, B)
    b = [val(v, i, B[i]) for i in range(n)]
    F1o = [j for j in F1 if j != o]
    Fs_choices = [()] if mut == "noFs" else [c for r in range(len(F1o) + 1) for c in itertools.combinations(F1o, r)]
    for r in range(len(J) + 1):
        for H in itertools.combinations(J, r):
            X = set(B[o]) | (set(J) - set(H))
            for Fs in Fs_choices:
                tau = []
                for i in range(n):
                    terms = [b[i]] if i != o else [0]
                    for q in Qm:
                        if q != o and q != i:
                            tot = val(v, i, B[q])
                            terms.append(max(tot - v[i][h] for h in B[q]))
                    if mut != "noTauFs":
                        for j in Fs:
                            (y,) = B[j]
                            if j != i and v[i][y] > b[i]:
                                terms.append(v[i][y])
                    tau.append(max(terms))
                needy = [i for i in range(n) if i != o and (tau[i] > b[i] or threatened(v, i, X, b[i]))]
                elig = [i for i in N1 + list(Fs) if i != o]
                if any(i not in elig for i in needy):                       # (C1)
                    continue
                if val(v, o, X) < tau[o]:                                   # (C2)
                    continue
                def edge(h, i):
                    if i not in needy:
                        return True
                    comp = (b[i] + v[i][h] >= tau[i]) or mut == "noComp"
                    return v[i][h] > 0 and comp and not threatened(v, i, X, b[i] + v[i][h])
                # (C3): a matching H -> elig covering every needy agent, with >= |H| - d edges
                Hl = list(H)
                found = False
                def rec(k, used, size):
                    nonlocal found
                    if found:
                        return
                    if k == len(Hl):
                        if all(i in used for i in needy) and size >= len(Hl) - d:
                            found = True
                        return
                    rec(k + 1, used, size)                                  # h unmatched (to a dummy)
                    for i in elig:
                        if i not in used and edge(Hl[k], i):
                            rec(k + 1, used | {i}, size + 1)
                rec(0, frozenset(), 0)
                if found:
                    return True
    return False

def G2(v, B):
    n = len(B); m = len(v[0]); J = set(range(m)) - set().union(*B)
    return not any(v[i][g] > val(v, i, B[i]) for i in range(n) for g in J)

def run(N, seed, mut=None):
    rng = random.Random(seed)
    from collections import Counter
    c = Counter(); ex = []
    for _ in range(N):
        n = rng.randint(3, 5)
        if _ % 2:
            m = rng.randint(n + 2, n + 3)
            v = [[0] * m for _ in range(n)]
            for i in range(n):
                for g, x in zip(rng.sample(range(m), rng.choice([3, 4])), rng.sample(range(1, 40), 4)):
                    v[i][g] = x
        else:
            m = rng.randint(n + 1, n + 4)
            v = [[0] * m for _ in range(n)]
            for i in range(n):
                for g, x in zip(rng.sample(range(m), rng.randint(2, min(4, m))), rng.sample(range(1, 40), 4)):
                    v[i][g] = x
        o_ = list(range(n)); rng.shuffle(o_)
        yd = sd(v, o_); Y = [yd[i] for i in range(n)]
        B0 = [({Y[i]} if Y[i] is not None else set()) for i in range(n)]
        states = [B0]
        J0 = set(range(m)) - set().union(*B0)
        ch = list(improving_chains(v, B0, J0)); rng.shuffle(ch)
        for s in ch[:2]:
            states.append(s)
            J1 = set(range(m)) - set().union(*s)
            ch2 = list(improving_chains(v, s, J1)); rng.shuffle(ch2)
            states.extend(ch2[:1])
        for B in states:
            J = set(range(m)) - set().union(*B)
            if len(J) > 5:
                continue
            if not G2(v, B):
                c["skipped_noG2"] += 1
                continue
            N1, F1, Qm = classes(v, B)
            c["states"] += 1
            c["states_with_frozen_singles"] += bool(F1)
            c["states_with_multigood"] += bool(Qm)
            for o in range(n):
                for d in (0, 1):
                    c["owner_tests"] += 1
                    bf = brute(v, B, o, d); fm = formula(v, B, o, d, mut)
                    c["brute_true"] += bf
                    if bf != fm:
                        c["MISMATCH"] += 1
                        if len(ex) < 5:
                            ex.append((mut, v, [sorted(x) for x in B], o, d, bf, fm))
    print(json.dumps(dict(source=f"Lemma M^c N={N} seed={seed} mutation={mut}", **dict(sorted(c.items())))))
    for e in ex:
        print("EXAMPLE", e)

if __name__ == "__main__":
    run(int(sys.argv[1]), int(sys.argv[2]), sys.argv[3] if len(sys.argv) > 3 else None)
