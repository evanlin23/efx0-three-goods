"""Draft and Exchange's moves (paper/k3-simple, Lemmas chain and ring) on a k = 3 state, in k3lib's format.

A DE state: every base is nothing, one good of the holder, or its pair {b, c}.  wants(i, g): i not a pair holder and g
ranked above its holding (or i holds nothing).  Free: not a pair holder, holding nothing or a good nobody wants.
  de_chains(rk, m, base): every DE chain (x holds a_x, b_x, c_x junk; x takes its pair, a_x passes along ANY
                          sequence of wanters to an agent whose good nobody wants, whose good becomes junk)
  de_rings(rk, m, base):  every DE ring (cycle of want arrows and pair arrows, distinct leftover goods)
  de_first(rk, m, base):  DE's own next trade (first x for a chain; else the pointer ring of the Improvement Lemma)
Each yields (new_base, description)."""
import itertools
from k3lib import bundles


def info(rk, m, base):
    n = len(rk); B = bundles(base, n); J = [g for g in range(m) if base[g] < 0]
    rank = [{g: t for t, g in enumerate(r)} for r in rk]
    U = [len(B[i]) == 2 for i in range(n)]
    def wants(i, g):
        if U[i] or g not in rank[i] or g in B[i]: return False
        if not B[i]: return True
        return rank[i][g] < rank[i][B[i][0]]
    wanters = {g: [i for i in range(n) if wants(i, g)] for g in range(m) if base[g] >= 0}
    free = [i for i in range(n) if not U[i] and (not B[i] or not wanters[B[i][0]])]
    return B, J, rank, U, wants, wanters, free


def blockers(rk, base, o, B, J):
    """agents x != o holding exactly a_x with b_x, c_x in J + B_o"""
    W = set(J) | set(B[o])
    return [x for x in range(len(rk)) if len(rk[x]) == 3 and x != o and B[x] == [rk[x][0]] and rk[x][1] in W and rk[x][2] in W]


def apply_cycle(base, cyc, recv):
    """cyc: agents w0..w_{k-1}; w_{t+1} receives the good of w_t plus recv[t+1] (a leftover good or None)"""
    nb = list(base); k = len(cyc)
    goods = [[g for g, a in enumerate(base) if a == w] for w in cyc]
    for t in range(k):
        for g in goods[t]: nb[g] = cyc[(t + 1) % k]
    for t, h in recv.items():
        if h is not None: nb[h] = cyc[t]
    return tuple(nb)


def de_chains(rk, m, base):
    n = len(rk); B, J, rank, U, wants, wanters, free = info(rk, m, base)
    out = []
    for x in range(n):
        if len(rk[x]) != 3 or B[x] != [rk[x][0]] or rk[x][1] not in J or rk[x][2] not in J: continue
        def walk(path):
            j = path[-1]; g = B[j][0] if B[j] else None
            ws = wanters.get(g, []) if g is not None else []
            if g is None or not ws:
                nb = list(base)
                if g is not None and j != x: nb[g] = -1
                for t in range(len(path) - 1, 0, -1):
                    nb[B[path[t - 1]][0]] = path[t]
                if len(path) == 1: nb[rk[x][0]] = -1
                nb[rk[x][1]] = x; nb[rk[x][2]] = x
                out.append((tuple(nb), ('DEchain', tuple(path))))
                return
            for w in ws:
                if w in path: continue   # a repeat gives a want ring, enumerated by de_rings
                walk(path + [w])
        walk([x])
    return out


def de_rings(rk, m, base):
    n = len(rk); B, J, rank, U, wants, wanters, free = info(rk, m, base)
    # arrows t -> u with the leftover good they use (None for want arrows)
    arrows = {t: [] for t in range(n)}
    for t in range(n):
        if U[t] or len(B[t]) != 1: continue
        y = B[t][0]
        if t in free:
            for x in blockers(rk, base, t, B, J):
                if len(B[x]) != 1: continue
                pair = {rk[x][1], rk[x][2]}
                if y in pair:
                    h = (pair - {y}).pop()
                    if h in J: arrows[t].append((x, h))
        else:
            for w in wanters[y]:
                if len(B[w]) == 1 or not B[w]: arrows[t].append((w, None))
    out = []
    for s in range(n):
        def dfs(path, hs, recv):
            t = path[-1]
            for (u, h) in arrows[t]:
                if h is not None and h in hs: continue
                if u == s and len(path) >= 2:
                    r = dict(recv); r[0] = h
                    out.append((apply_cycle(base, path, r), ('DEring', tuple(path), tuple(r.get(i) for i in range(len(path))))))
                elif u > s and u not in path:
                    r = dict(recv); r[len(path)] = h
                    dfs(path + [u], hs | ({h} if h is not None else set()), r)
        dfs([s], set(), {})
    return out


def de_first(rk, m, base):
    """DE's next trade (Algorithm DE): first chain agent, else the pointer ring (first blockers, distinct q's)"""
    n = len(rk); B, J, rank, U, wants, wanters, free = info(rk, m, base)
    for x in range(n):
        if len(rk[x]) == 3 and B[x] == [rk[x][0]] and rk[x][1] in J and rk[x][2] in J:
            j = [x]
            while True:
                g = B[j[-1]][0] if B[j[-1]] else None
                ws = wanters.get(g, []) if g is not None else []
                if not ws: break
                if ws[0] in j:
                    cyc = j[j.index(ws[0]):]
                    return apply_cycle(base, cyc, {}), ('DEfirst-wantring', tuple(cyc))
                j.append(ws[0])
            nb = list(base); g = B[j[-1]][0] if B[j[-1]] else None
            if g is not None and len(j) > 1: nb[g] = -1
            for t in range(len(j) - 1, 0, -1): nb[B[j[t - 1]][0]] = j[t]
            if len(j) == 1: nb[rk[x][0]] = -1
            nb[rk[x][1]] = x; nb[rk[x][2]] = x
            return tuple(nb), ('DEfirst-chain', tuple(j))
    # pointer ring
    if all(U): return None
    q = {}; xs = {}
    for o in free:
        if not B[o]: return None   # can finish
        bl = blockers(rk, base, o, B, J)
        for x in bl:
            h = ({rk[x][1], rk[x][2]} - set(B[o])).pop()
            if h not in q.values():
                xs[o] = x; q[o] = h; break
        else:
            return None
    sigma = {}
    for j in range(n):
        if U[j]: continue
        sigma[j] = xs[j] if j in free else wanters[B[j][0]][0]
    j = next(i for i in range(n) if not U[i]); seen = []
    while j not in seen:
        seen.append(j); j = sigma[j]
    cyc = seen[seen.index(j):]
    recv = {}
    for t, w in enumerate(cyc):
        if w in free: recv[(t + 1) % len(cyc)] = q[w]
    return apply_cycle(base, cyc, recv), ('DEfirst-ring', tuple(cyc))


def de_can_finish(rk, m, base):
    """Definition finish of paper/k3-simple: some free o and H subset of J, |H| <= |F| - 1, hitting {b_x, c_x} for
    every blocker x of o; or every agent holds its pair.  Returns (o, H) or None.  Works without (NC)."""
    n = len(rk); B, J, rank, U, wants, wanters, free = info(rk, m, base)
    if all(U): return (0, ())
    for o in free:
        bl = blockers(rk, base, o, B, J)
        need = [tuple(g for g in (rk[x][1], rk[x][2]) if g in J) for x in bl]
        if any(not s for s in need): continue   # both in Y_o: impossible since o holds at most one good
        # least hitting set by brute force over subsets of the goods involved
        goods = sorted(set(g for s in need for g in s))
        best = None
        for r in range(0, len(free)):
            for Hs in itertools.combinations(goods, r):
                if all(set(s) & set(Hs) for s in need): best = Hs; break
            if best is not None: break
        if best is not None: return (o, best)
    return None


def de_trades(rk, m, base):
    return de_chains(rk, m, base) + de_rings(rk, m, base)
