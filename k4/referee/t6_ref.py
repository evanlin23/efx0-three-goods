#!/usr/bin/env python3
"""Referee check of Lemma T6 and its certificate corollary (k4/ttc.md §14.2, branch claude/k4-ttc at 71c7b83). Own
code, raw EFX0; nothing from k4/ttc/ is run.

1. Lemma T6 on random perfect SD starts (n = 3..5, <= 4 relevant goods): every move (addition; chain with nonempty
   passed bases, H sets in the junk and the receivers' relevant goods, x0 taking junk and possibly the end's pick;
   ring: a cycle in which every member takes its predecessor's base plus junk), every completion keeping the new bases
   (ANY completion, EFX0 or not): (a) value domination, (b) <= 2 foreign picks per bundle, (c) the two-pick shape.
2. The corollary's soundness on the same data: whenever every MD EFX0 allocation has a blocked agent, no one-move
   state has any EFX0 completion.
3. The certificate on the 11 n = 4 OC1^max counterexamples (results/k4_oc1max/oc1max_cex_n4.json of
   compute/k4-oc1max-cert): every MD EFX0 allocation has a blocked agent (instance 0 = 4_n4_3 #58 printed in full).
"""
import itertools, random, sys, json
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, efx0, rel, sd, mk

def subsets(S):
    S = sorted(S)
    for k in range(len(S) + 1):
        for c in itertools.combinations(S, k):
            yield set(c)

def moves_desc(v, Y):
    """(kind, path, H list, new bases) for every move from the picks Y (perfect)."""
    n = len(Y); m = len(v[0]); J = set(range(m)) - set(Y); R = [rel(v, i) for i in range(n)]
    B = [{y} for y in Y]; p = [v[i][Y[i]] for i in range(n)]
    out = []
    for x in range(n):
        for H in subsets(J & R[x]):
            if H:
                c = [set(b) for b in B]; c[x] |= H; out.append(("add", (x,), [H], c))
    for t in range(1, n):
        for seq in itertools.permutations(range(n), t + 1):
            def rec(i, used, Hs, c):
                if i > t:
                    for H0 in subsets(((J - used) | B[seq[-1]]) & R[seq[0]]):
                        if H0 and val(v, seq[0], H0) > p[seq[0]]:
                            c2 = [set(b) for b in c]; c2[seq[0]] = set(H0)
                            out.append(("chain", seq, [H0] + Hs, c2))
                    return
                xi = seq[i]
                for Hi in subsets((J - used) & R[xi]):
                    if val(v, xi, B[seq[i - 1]] | Hi) > p[xi]:
                        c2 = [set(b) for b in c]; c2[xi] = B[seq[i - 1]] | Hi
                        rec(i + 1, used | Hi, Hs + [Hi], c2)
            rec(1, set(), [], [set(b) for b in B])
    for r in range(2, n + 1):
        for cyc in itertools.permutations(range(n), r):
            if cyc[0] != min(cyc):
                continue
            def ring(i, used, Hs, c):
                if i == r:
                    out.append(("ring", cyc, Hs, c)); return
                w, pred = cyc[i], cyc[i - 1]
                for Hw in subsets((J - used) & R[w]):
                    if val(v, w, B[pred] | Hw) > p[w]:
                        c2 = [set(b) for b in c]; c2[w] = B[pred] | Hw
                        ring(i + 1, used | Hw, Hs + [Hw], c2)
            ring(0, set(), [], [set(b) for b in B])
    return out

def completions(B, n, m):
    J = sorted(set(range(m)) - set().union(*B))
    for f in itertools.product(range(n), repeat=len(J)):
        X = [set(b) for b in B]
        for g, a in zip(J, f):
            X[a].add(g)
        yield X

def foreign(Y, X, i):
    return [Y[j] for j in range(len(Y)) if j != i and Y[j] in X[i]]

def blocked(v, Y, T, J):
    n = len(Y)
    for i in range(n):
        f = foreign(Y, T, i)
        if len(f) >= 3:
            return i
        if len(f) == 2:
            jr = val(v, i, J & rel(v, i))
            if all(v[i][P] + jr <= v[i][Y[i]] for P in f):
                return i
    return None

def check_T6(v, Y, c, ex):
    n = len(Y); m = len(v[0]); J = set(range(m)) - set(Y); p = [v[i][Y[i]] for i in range(n)]
    states_efx = False
    for kind, path, Hs, Bn in moves_desc(v, Y):
        c["moves"] += 1
        for X in completions(Bn, n, m):
            c["move_completions"] += 1
            ok = all(val(v, i, X[i]) >= p[i] for i in range(n))
            for i in range(n):
                f = foreign(Y, X, i)
                if len(f) > 2:
                    ok = False
                if len(f) == 2:
                    if kind != "chain" or i not in path[1:] or Y[path[-1]] not in X[i]:
                        ok = False
                    else:
                        jx = path.index(i)
                        if not (v[i][Y[path[jx - 1]]] + val(v, i, Hs[jx]) > p[i]):
                            ok = False
            if not ok:
                c["T6_fail"] += 1
                if len(ex) < 5:
                    ex.append(("T6", v, Y, kind, path, [sorted(h) for h in Hs], [sorted(x) for x in X]))
            if efx0(v, X):
                states_efx = True
    return states_efx

def all_alloc(n, m):
    for f in itertools.product(range(n), repeat=m):
        yield [{g for g in range(m) if f[g] == i} for i in range(n)]

def run(N, seed):
    rng = random.Random(seed)
    from collections import Counter
    c = Counter(); ex = []
    for _ in range(N):
        n = rng.randint(3, 5); m = rng.randint(n + 1, n + 3)
        v = [[0] * m for _ in range(n)]
        for i in range(n):
            for g, x in zip(rng.sample(range(m), rng.randint(2, min(4, m))), rng.sample(range(1, 40), 4)):
                v[i][g] = x
        orders = list(itertools.permutations(range(n))); rng.shuffle(orders)
        seen = set()
        for o in orders[:3]:
            Y = sd(v, o)
            if tuple(Y) in seen or any(y is None for y in Y):
                continue
            seen.add(tuple(Y)); c["starts"] += 1
            one_move_efx = check_T6(v, Y, c, ex)
            if m <= 7:
                J = set(range(m)) - set(Y); p = [v[i][Y[i]] for i in range(n)]
                TT = [T for T in all_alloc(n, m) if efx0(v, T) and all(val(v, i, T[i]) >= p[i] for i in range(n))]
                if TT and all(blocked(v, Y, T, J) is not None for T in TT):
                    c["certificate_starts"] += 1
                    if one_move_efx:
                        c["corollary_fail"] += 1; ex.append(("corollary", v, Y))
    print(json.dumps(dict(source=f"Lemma T6 N={N} seed={seed}", **dict(sorted(c.items())))))
    for e in ex[:5]:
        print("EXAMPLE", e)

def cex(path):
    import ast
    d = json.load(open(path)); insts = d["instances"]
    if isinstance(insts, str):
        insts = ast.literal_eval(insts)
    for I in insts:
        v = mk(I["sets"], I["vals"]); n = len(v); m = len(v[0]); Y = I["picks"]
        J = set(range(m)) - set(Y); p = [v[i][Y[i]] for i in range(n)]
        E = [T for T in all_alloc(n, m) if efx0(v, T)]
        TT = [T for T in E if all(val(v, i, T[i]) >= p[i] for i in range(n))]
        bl = [blocked(v, Y, T, J) for T in TT]
        r = dict(core=f"{I['list']}#{I['idx']}", efx0=len(E), md_efx0=len(TT), every_target_blocked=all(b is not None for b in bl),
                 blocked_agents=sorted(set(b for b in bl if b is not None)))
        if I["idx"] == 58:
            r["targets"] = [[sorted(x) for x in T] for T in TT]
        print(json.dumps(r))

if __name__ == "__main__":
    if sys.argv[1] == "cex":
        cex(sys.argv[2])
    else:
        run(int(sys.argv[1]), int(sys.argv[2]))
