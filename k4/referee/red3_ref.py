#!/usr/bin/env python3
"""Referee check of Lemmas MAX3 and RED3 (k4/k3_oc1.md §11, branch claude/k4-k3-oc1 at 974853c). Own code, raw EFX0.

SD starts whose picks form a maximum matching but leave some agent pickless, in random instances with <= 3 relevant
goods per agent (also <= 4, where the same argument applies: RED of k4/sdc.md §31). U = pickless agents, S = agents
reachable from U by alternating paths, T = the rest.
  MAX3: no agent of U ∪ S values a junk good; every good valued by U ∪ S is the pick of an agent of S (S closed).
  RED3: in I' (agents T ∪ U, U null; goods {Y_t} ∪ J), (1) the SD of the order restricted to T ∪ U is (Y_t);
        (2) every official move of I' from Y' is an official move of I from Y;
        (3) every one-absorber EFX0 completion of Y' or of a one-move state of I' extends (S keep their picks as
            singletons) to a one-absorber EFX0 completion of I.
"""
import itertools, random, sys, json
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, efx0, rel, sd, nu, moves

def oa_completions(v, B):
    n = len(B); m = len(v[0]); J = sorted(set(range(m)) - set().union(*B))
    for f in itertools.product(range(n), repeat=len(J)):
        cnt = [0] * n
        for a in f:
            cnt[a] += 1
        if sum(1 for x in cnt if x >= 2) > 1:
            continue
        X = [set(b) for b in B]
        for g, a in zip(J, f):
            X[a].add(g)
        if efx0(v, X):
            yield X

def run(N, kmax, seed):
    rng = random.Random(seed)
    from collections import Counter
    c = Counter(); ex = []
    for _ in range(N):
        n = rng.randint(3, 6); m = rng.randint(n - 1, n + 2)
        v = [[0] * m for _ in range(n)]
        for i in range(n):
            for g, x in zip(rng.sample(range(m), rng.randint(1, min(kmax, m))), rng.sample(range(1, 30), kmax)):
                v[i][g] = x
        nv = nu(v)
        for o in itertools.permutations(range(n)):
            Y = sd(v, o)
            npk = sum(1 for y in Y if y is not None)
            if npk != nv or npk == n:
                continue
            U = [i for i in range(n) if Y[i] is None]
            holder = {Y[i]: i for i in range(n) if Y[i] is not None}
            S = set(); frontier = list(U)
            while frontier:
                a = frontier.pop()
                for g in rel(v, a):
                    if g in holder and holder[g] not in S:
                        S.add(holder[g]); frontier.append(holder[g])
            J = set(range(m)) - set(holder)
            if len(J) > 5:
                continue
            c["starts"] += 1
            T = [i for i in range(n) if i not in S and i not in U]
            # MAX3
            if any(v[a][g] > 0 for a in list(S) + U for g in J):
                c["MAX3_fail"] += 1; ex.append(("MAX3", v, Y))
            if any(g in holder and holder[g] not in S for a in list(S) + U for g in rel(v, a)):
                c["MAX3_closed_fail"] += 1; ex.append(("closed", v, Y))
            # I'
            ag = T + U; goods = sorted({Y[t] for t in T} | J)
            vr = [[(v[a][g] if a in T else 0) for g in goods] for a in ag]
            # (1) SD of the restricted order
            o_r = [ag.index(a) for a in o if a in ag]
            Yr = sd(vr, o_r)
            exp = [goods.index(Y[a]) if a in T else None for a in ag]
            c["red1_tests"] += 1
            if Yr != exp:
                c["RED3_1_fail"] += 1; ex.append(("RED1", v, Y, o))
            Br = [({goods.index(Y[a])} if a in T else set()) for a in ag]
            # (2) moves of I' are moves of I
            full = {tuple(frozenset(b) for b in s) for s in moves(v, [({y} if y is not None else set()) for y in Y])}
            def lift(Cr):
                C = [set() for _ in range(n)]
                for idx, a in enumerate(ag):
                    C[a] = {goods[g] for g in Cr[idx]}
                for s in S:
                    C[s] = {Y[s]}
                return C
            mv = moves(vr, Br)
            for Cr in mv:
                c["red2_moves"] += 1
                if tuple(frozenset(b) for b in lift(Cr)) not in full:
                    c["RED3_2_fail"] += 1; ex.append(("RED2", v, Y))
            # (3) completions extend
            for Cr in [Br] + mv:
                C = lift(Cr)
                for Xr in oa_completions(vr, Cr):
                    X = lift(Xr)
                    c["red3_completions"] += 1
                    if not efx0(v, X) or sum(1 for i in range(n) if len(X[i] - C[i]) >= 2) > 1:
                        c["RED3_3_fail"] += 1; ex.append(("RED3", v, Y))
    print(json.dumps(dict(source=f"MAX3 / RED3 N={N} kmax={kmax} seed={seed}", **dict(sorted(c.items())))))
    for e in ex[:5]:
        print("EXAMPLE", e)

if __name__ == "__main__":
    run(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
