"""Rank-based engine for the reduction experiments (k3/simplify/explore/reductions/NOTES.md). EVIDENCE only.

Input everywhere: rank[i] = (a_i, b_i, c_i), agent i's three goods, best first, on goods 0..m-1 (goods nobody ranks
are worthless). Every agent is balanced, so EFX0 is ordinal (Lemma L5) and is checked with the values 4, 3, 2 by
k3s.efx0 (the raw definition).

`k3s_like(rank, m, leader, absorber)` is K3S steps 1-3 (draft with peel priority, upgrade loop, HitSet + one absorber)
with two plug points and NO rotation:
  leader(rank, m, unproc, free, Y, U) -> (x, mode)   mode 'top' (K3S: x takes its top) or 'pair' (x takes {b_x, c_x})
  absorber: 'r' (K3S: the last non-upgraded agent of the draft) or 'any' (r first, then every agent in index order).
It returns X (X[g] = owner) or None when no tried absorber is valid. With leader_index_top and absorber 'r' it equals
k3s.k3s(..., rotate=False) (checked by `python3 engine.py`).
"""
import os, sys, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..'))
from k3s import k3s, efx0  # noqa: E402

VAL = (4, 3, 2)
def vals(rank): return [dict(zip(r, VAL)) for r in rank]
def ok(rank, m, X): return X is not None and efx0(len(rank), m, vals(rank), X)

def gen_small(n, m):
    """every ranking profile with n agents on m goods; agent 0 ranks 0 > 1 > 2 (as k3/simplify/test_k3s.py)"""
    tri = list(itertools.permutations(range(m), 3))
    for rest in itertools.product(tri, repeat=n - 1):
        yield [(0, 1, 2)] + list(rest)

# ------------------------------------------------------------------------------------------------ leader rules
def leader_index_top(rank, m, unproc, free, Y, U): return unproc[0], 'top'

def leader_index_pair(rank, m, unproc, free, Y, U): return unproc[0], 'pair'

def nvaluers(rank, unproc, g): return sum(g in rank[j] for j in unproc)

def leader_hub_top(rank, m, unproc, free, Y, U):
    """'pre-assign the hubs': the leader is an agent whose top has the most unprocessed valuers"""
    return min(unproc, key=lambda x: (-nvaluers(rank, unproc, rank[x][0]), x)), 'top'

def leader_pair_safe(rank, m, unproc, free, Y, U):
    """a pair leader whose b and c are nobody else's top (unprocessed); else the index agent takes its top"""
    tops = {rank[j][0] for j in unproc}
    for x in unproc:
        if rank[x][1] not in tops and rank[x][2] not in tops: return x, 'pair'
    return unproc[0], 'top'

def leader_pair_c_only(rank, m, unproc, free, Y, U):
    """a pair leader whose b and c are the c of every other unprocessed agent that values them (so nobody can ever
    need them alone); else the index agent takes its top"""
    for x in unproc:
        if all(rank[j][2] == g for j in unproc if j != x for g in rank[x][1:] if g in rank[j]): return x, 'pair'
    return unproc[0], 'top'

# ------------------------------------------------------------------------------------------------ K3S steps 1-3
def draft(rank, m, leader):
    n = len(rank); free = set(range(m)); unproc = list(range(n)); order = []; Y = [None] * n; U = []; L = []
    while unproc:
        i = next((j for j in unproc if sum(g in free for g in rank[j]) <= 2), None)
        mode = 'top'
        if i is None:
            i, mode = leader(rank, m, unproc, free, Y, U); L.append((i, mode))
        if mode == 'pair':
            Y[i] = rank[i][1]; free -= {rank[i][1], rank[i][2]}; U.append(i)
        else:
            Y[i] = next((g for g in rank[i] if g in free), None); free.discard(Y[i])
        order.append(i); unproc.remove(i)
    return order, Y, U, L

def needs(rank, i, Y, U):
    if i in U: return ()
    if Y[i] is None: return rank[i]
    return rank[i][:rank[i].index(Y[i])]

def NA(rank, Y, U): return {g for i in range(len(rank)) for g in needs(rank, i, Y, U)}

def junk(rank, m, Y, U):
    used = {g for g in Y if g is not None} | {rank[u][2] for u in U}
    return [g for g in range(m) if g not in used]

def upgrades(rank, m, Y, U):
    U = list(U)
    while True:
        J = set(junk(rank, m, Y, U)); na = NA(rank, Y, U)
        k = next((k for k in range(len(rank)) if k not in U and Y[k] == rank[k][1] and rank[k][2] in J
                  and rank[k][1] not in na), None)
        if k is None: return U
        U.append(k)

def absorb(rank, m, o, Y, U):
    n = len(rank); J = junk(rank, m, Y, U); Js = set(J); na = NA(rank, Y, U)
    W = Js | ({rank[o][1], rank[o][2]} if o in U else ({Y[o]} if Y[o] is not None else set()))
    E = [x for x in range(n) if x != o and x not in U and Y[x] == rank[x][0] and rank[x][1] in W and rank[x][2] in W]
    if any(rank[z][1] not in Js and rank[z][2] not in Js for z in E): return None
    one = lambda z: rank[z][1] if rank[z][1] in Js else rank[z][2]
    H = None
    for x in E:
        for y in E:
            if x != y and H is None:
                for g in rank[x][1:]:
                    if g in Js and g in rank[y][1:]:
                        H = [g] + [one(z) for z in E if z not in (x, y)]; break
    if H is None: H = [one(z) for z in E]
    H = list(dict.fromkeys(H))
    cap = [0 if (i in U or (Y[i] is not None and Y[i] in na)) else 1 for i in range(n)]
    if len(H) > sum(cap) - cap[o]: return None
    X = [None] * m
    for i in range(n):
        if Y[i] is not None: X[Y[i]] = i
    for u in U: X[rank[u][2]] = u
    for i in range(n):
        if i != o and cap[i] and H: X[H.pop(0)] = i
    for g in J:
        if X[g] is None: X[g] = o
    return X

def k3s_like(rank, m, leader=leader_index_top, absorber='r', info=None):
    order, Y, U, L = draft(rank, m, leader)
    U = upgrades(rank, m, Y, U)
    nonU = [i for i in order if i not in U]
    r = nonU[-1] if nonU else order[-1]
    cands = [r] + ([o for o in range(len(rank)) if o != r] if absorber == 'any' else [])
    if info is not None: info.update(order=order, Y=Y, U=U, leaders=L, r=r)
    for o in cands:
        X = absorb(rank, m, o, Y, U)
        if X is not None:
            if info is not None: info['o'] = o
            return X
    return None

if __name__ == '__main__':
    # validation: index leaders + absorber r == k3s.k3s(rotate=False)
    cnt = 0
    for n, m in [(2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (3, 6)]:
        for rank in gen_small(n, m):
            X1 = k3s(n, m, vals(rank), rotate=False); X2 = k3s_like(rank, m)
            assert X1 == X2, (rank, m, X1, X2); cnt += 1
    print(f"engine == k3s(rotate=False) on all {cnt} profiles with n = 2, m <= 5 and n = 3, m <= 6")
