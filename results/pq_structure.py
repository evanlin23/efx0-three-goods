#!/usr/bin/env python3
"""Structural facts used in proofs/pq_bounded.md (workstream proof/lit-pq).

For the 6 graphical all-P4 cores of K4.MC7 (read from k4/MINCEX.md §8) and for the cores H_1..H_5 of
k4/c4.md §7 (PR #33's branch proof/k4-c4; rebuilt here from that definition), print:
  n, m; p = largest number of agents valuing one good; q = largest number of goods two agents share;
  parallel pairs (agent pairs sharing >= 2 goods); whether the agent graph (agents adjacent iff they share a good)
  is simple (q <= 1) and bipartite; its number of triangles and girth; and the Berge girth of the hypergraph whose
  vertices are the agents and whose hyperedges are the goods (length of the shortest cycle
  v1 e1 v2 e2 ... vL eL v1 with distinct agents v and distinct goods e, L >= 2; goods valued by one agent are ignored).
For cores 4 and 5 it also checks that every agent's private good can be put on a distinct non-adjacent agent pair
(so that the instance is a simple-graph instance in the sense of CFKS).

Values do not matter here; only who values what. Run from the repository root:  python3 results/pq_structure.py
"""
import itertools
import re
from collections import deque


def cores_k4_mc7(path="k4/MINCEX.md"):
    text = open(path, encoding="utf-8").read()
    sec = text[text.index("The 6 cores (n = 6, m = 15"):]
    found = re.findall(r"^(\d)\. (\[\[.*?\]\])", sec, re.M)[:6]
    assert [lab for lab, _ in found] == list("123456"), found
    return [(f"core {lab}", eval(lst)) for lab, lst in found]


def H(t):
    """k4/c4.md §7: agents l, x_{j,i} (1<=i<=3), y_j for 1<=j<=t; R_l = {g1, z, u, u'},
    R_{x_{j,i}} = {a_{j,i}, b_{j,i}, c_{j,i}, g_j}, R_{y_j} = {a_{j,1}, a_{j,2}, a_{j,3}, e_j}, e_j = g_{j+1} (j<t), e_t = z."""
    R = [["g1", "z", "u", "u'"]]
    for j in range(1, t + 1):
        for i in range(1, 4):
            R.append([f"a{j},{i}", f"b{j},{i}", f"c{j},{i}", f"g{j}"])
        R.append([f"a{j},1", f"a{j},2", f"a{j},3", f"g{j + 1}" if j < t else "z"])
    return R


def analyse(R):
    n = len(R)
    goods = sorted({g for r in R for g in r}, key=str)
    val = {g: [i for i in range(n) if g in R[i]] for g in goods}
    p = max(len(v) for v in val.values())
    share = {(a, b): set(R[a]) & set(R[b]) for a, b in itertools.combinations(range(n), 2)}
    q = max(len(s) for s in share.values())
    parallel = [ab for ab, s in share.items() if len(s) >= 2]
    nb = {i: set() for i in range(n)}
    for (a, b), s in share.items():
        if s:
            nb[a].add(b)
            nb[b].add(a)
    # bipartite (all components)
    col, bip = {}, True
    for s0 in range(n):
        if s0 in col:
            continue
        col[s0] = 0
        dq = deque([s0])
        while dq:
            u = dq.popleft()
            for w in nb[u]:
                if w not in col:
                    col[w] = 1 - col[u]
                    dq.append(w)
                elif col[w] == col[u]:
                    bip = False
    tri = sum(1 for a, b, c in itertools.combinations(range(n), 3) if b in nb[a] and c in nb[b] and a in nb[c])
    # girth of the simple agent graph (BFS from every vertex)
    girth = None
    for s0 in range(n):
        dist, par = {s0: 0}, {s0: None}
        dq = deque([s0])
        while dq:
            u = dq.popleft()
            for w in nb[u]:
                if w not in dist:
                    dist[w], par[w] = dist[u] + 1, u
                    dq.append(w)
                elif par[u] != w:
                    c = dist[u] + dist[w] + 1
                    girth = c if girth is None else min(girth, c)
    # Berge girth: shortest cycle with distinct agents and distinct shared goods (length >= 2)
    shared_goods = [g for g in goods if len(val[g]) >= 2]
    berge = None
    for L in range(2, 8):
        if cycle_exists(R, val, shared_goods, L, n):
            berge = L
            break
    return dict(n=n, m=len(goods), p=p, q=q, parallel=parallel, simple=(q <= 1), bipartite=bip,
                triangles=tri, girth=girth, berge=berge, nb=nb)


def cycle_exists(R, val, shared_goods, L, n):
    """Is there v1 e1 ... vL eL v1 with distinct agents and distinct goods, e_k containing v_k and v_{k+1}?"""
    goods_of = {i: [g for g in shared_goods if i in val[g]] for i in range(n)}

    def dfs(path, used, start):
        u = path[-1]
        for g in goods_of[u]:
            if g in used:
                continue
            for w in val[g]:
                if w == u:
                    continue
                if len(path) == L and w == start:
                    return True
                if len(path) < L and w not in path and w > start:
                    if dfs(path + [w], used | {g}, start):
                        return True
        return False

    return any(dfs([s], frozenset(), s) for s in range(n))


def private_goods_fit_simple(R, nb):
    """Can every agent's private good be placed on a distinct non-adjacent agent pair (one per agent)?"""
    n = len(R)
    counts = {g: sum(g in r for r in R) for r in R for g in r}
    owners = [i for i in range(n) if any(counts[g] == 1 for g in R[i])]
    nonadj = [frozenset((a, b)) for a, b in itertools.combinations(range(n), 2) if b not in nb[a]]
    options = [[e for e in nonadj if i in e] for i in owners]
    for choice in itertools.product(*options):
        if len(set(choice)) == len(owners):
            return True
    return False


def main():
    rows = cores_k4_mc7() + [(f"H_{t}", H(t)) for t in range(1, 6)]
    print("instance | n | m | p | q | parallel pairs | simple | bipartite | triangles | girth (simple graph) | Berge girth")
    for name, R in rows:
        a = analyse(R)
        par = ", ".join(f"({x},{y})" for x, y in a["parallel"]) or "none"
        print(f"{name} | {a['n']} | {a['m']} | {a['p']} | {a['q']} | {par} | {a['simple']} | {a['bipartite']} | "
              f"{a['triangles']} | {a['girth']} | {a['berge']}")
        if name in ("core 4", "core 5"):
            print(f"  {name}: private goods fit on distinct non-adjacent pairs: {private_goods_fit_simple(R, a['nb'])}")
    for t in range(1, 6):
        a = analyse(H(t))
        assert (a["n"], a["m"], a["p"], a["q"], a["berge"]) == (4 * t + 1, 10 * t + 3, 4, 1, 3), (t, a)
    print("check: H_t has n = 4t + 1, m = 10t + 3, p = 4, q = 1, Berge girth 3 for t = 1..5: OK")


if __name__ == "__main__":
    main()
