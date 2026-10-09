"""Idea 3 (a combinatorial formulation): the K3S rotation is a Pareto improvement. Is Pareto optimality enough?

A *state* gives each agent i one of: nothing, one own good (a_i, b_i or c_i), or its pair {b_i, c_i} (i in U).
Utility order (balanced agents, a < b + c): pair > a > b > c > nothing. A state is *valid* if
  (V0) the goods held are distinct;
  (V1) every good that some non-U agent ranks above its holding (NA, "needed alone") is held as the single good of
       another non-U agent;
  (V2) no good of a pair is in NA.
These are the states K3S reaches before its absorber step (draft + upgrades, and after the rotation, Theorem B).
A valid state is *completable* if some absorber o passes K3S's HitSet test (engine.absorb), which then yields an
EFX0 allocation (proofs/k3_simple.md §3.4).

The K3S rotation moves every agent of the need chain up (k: a -> pair; the others to a good they need), so a valid
state in which K3S rotates is not Pareto optimal among valid states. Tested here:
  H-PO   every Pareto-optimal valid state is completable;
  H-MAX  the valid state maximising sum u_i (u: pair 4, a 3, b 2, c 1, nothing 0) is completable (some maximiser,
         and every maximiser);
  H-LEX  the leximin-optimal valid state ... ; plus the count of profiles with no completable valid state at all
         (must be 0: K3S's output is one).
Usage: python3 po_states.py [n m]...
"""
import sys, itertools, time
from engine import absorb, ok, gen_small, NA

def states(rank, m):
    n = len(rank)
    opts = [[None, ('g', r[0]), ('g', r[1]), ('g', r[2]), ('p',)] for r in rank]
    for choice in itertools.product(*opts):
        used = []; Y = [None] * n; U = []; u = []
        for i, c in enumerate(choice):
            if c is None: u.append(0); continue
            if c[0] == 'g': Y[i] = c[1]; used.append(c[1]); u.append(3 - rank[i].index(c[1]))
            else: Y[i] = rank[i][1]; U.append(i); used += [rank[i][1], rank[i][2]]; u.append(4)
        if len(set(used)) < len(used): continue
        na = NA(rank, Y, U)
        singles = {Y[j] for j in range(n) if j not in U and Y[j] is not None}
        if not na <= singles: continue
        if any(rank[x][1] in na or rank[x][2] in na for x in U): continue
        yield Y, U, tuple(u)

UNSOUND = [0]
def completable(rank, m, Y, U):
    """some absorber o that is free (in U, holds nothing, or holds a good nobody needs alone) passes the HitSet test
    and the completion is EFX0 by the raw check (UNSOUND counts HitSet passes whose output is not EFX0)"""
    na = NA(rank, Y, U)
    for o in range(len(rank)):
        if o not in U and Y[o] is not None and Y[o] in na: continue
        X = absorb(rank, m, o, Y, U)
        if X is not None:
            if ok(rank, m, X): return True
            UNSOUND[0] += 1
    return False

def dominated(u, w): return all(a <= b for a, b in zip(u, w)) and u != w

def analyse(rank, m):
    S = list(states(rank, m))
    comp = [completable(rank, m, Y, U) for Y, U, _ in S]
    us = [u for _, _, u in S]
    po = [k for k in range(len(S)) if not any(dominated(us[k], us[j]) for j in range(len(S)))]
    best = max(sum(u) for u in us); mx = [k for k in range(len(S)) if sum(us[k]) == best]
    lexkey = lambda u: sorted(u); lb = max(lexkey(u) for u in us); lx = [k for k in range(len(S)) if lexkey(us[k]) == lb]
    return dict(anycomp=any(comp), po_all=all(comp[k] for k in po), po_some=any(comp[k] for k in po),
                max_all=all(comp[k] for k in mx), max_some=any(comp[k] for k in mx),
                lex_all=all(comp[k] for k in lx), lex_some=any(comp[k] for k in lx),
                po_bad=[S[k][:2] for k in po if not comp[k]][:1])

if __name__ == '__main__':
    args = list(map(int, sys.argv[1:])) or [3, 4, 3, 5, 3, 6, 3, 7]
    t = time.time()
    for n, m in zip(args[::2], args[1::2]):
        cnt = dict.fromkeys(['tot', 'anycomp', 'po_all', 'po_some', 'max_all', 'max_some', 'lex_all', 'lex_some'], 0)
        ex = {}
        for rank in gen_small(n, m):
            r = analyse(rank, m); cnt['tot'] += 1
            for k in cnt:
                if k != 'tot':
                    cnt[k] += r[k]
                    if not r[k] and k not in ex: ex[k] = (rank, r['po_bad'] if k.startswith('po') else None)
        print(f"n={n} m={m}: {cnt} unsound HitSet passes {UNSOUND[0]}  [{time.time() - t:.0f}s]", flush=True)
        for k, v in ex.items(): print(f"   first profile failing {k}: {v}", flush=True)
