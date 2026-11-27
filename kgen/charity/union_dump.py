"""Proposition DU (kgen/charity.md §6): if the agent-good incidence graph has at least two components that contain
agents, a complete EFX0 allocation exists.  Recipe: in every component run CKMS (chlib.ckms: an EFX0 state with
strong charity and an acyclic envy graph, so with a source); then put the unallocated goods of every component onto a
source of some other component, and goods valued by nobody onto any source.  This script builds the allocation
exactly by the recipe and checks it with the raw EFX0 definition (chlib.efx0), on
  - disjoint unions of 2..4 random instances (k = 2..6),
  - disjoint unions of copies of the stranded instances GM4-E, GM4-G, S(3, 3), S'(3, 3), with their stranded states
    taken as the per-component states (they have strong charity; their sources are computed).

    python3 kgen/charity/union_dump.py SEED T"""
import sys, random, collections
from chlib import Inst, rand_inst, ckms, efx0, pool_ok, pool_of, sources, envy_graph
from stuck_family import build


def union(parts):
    """parts: list of (Inst, state X).  Returns the union instance and the per-part offsets."""
    v = []; X = []; off = 0; offs = []; aoff = 0; aoffs = []
    for I, Xp in parts:
        offs.append(off); aoffs.append(aoff)
        v += [{g + off: x for g, x in vi.items()} for vi in I.v]
        X += [{g + off for g in B} for B in Xp]
        off += I.m; aoff += I.n
    return Inst(len(v), off, v), X, offs, aoffs


def dump(parts):
    U, X, offs, aoffs = union(parts)
    c = len(parts)
    srcs = []
    for r, (I, Xp) in enumerate(parts):
        S = sources(I, Xp); assert S, 'every component state has a source'
        srcs.append(aoffs[r] + S[0])
    for r, (I, Xp) in enumerate(parts):
        P = {g + offs[r] for g in pool_of(I, Xp)}
        X[srcs[(r + 1) % c]] |= P                           # onto a source of the next component
    assert not pool_of(U, X)
    return U, X


if __name__ == '__main__':
    seed, T = map(int, sys.argv[1:3]); rng = random.Random(seed); C = collections.Counter()
    print('$ python3 kgen/charity/union_dump.py', *sys.argv[1:], flush=True)
    for t in range(T):
        parts = []
        for r in range(rng.randint(2, 4)):
            n = rng.randint(1, 5); K = rng.randint(2, 6)
            I = rand_inst(rng, n, rng.randint(n, 2 * n + 2), 1, K, vmax=12, cover=False)
            Xp, P, cnt, tab = ckms(I, rng=rng)
            assert efx0(I, Xp) and pool_ok(I, Xp, P)
            C['components with a nonempty CKMS pool'] += bool(P)
            parts.append((I, Xp))
        U, X = dump(parts)
        ok = efx0(U, X)
        C['random unions: complete EFX0 by the recipe %s' % ok] += 1
    GM4E = Inst(4, 7, [{0: 3, 2: 10, 4: 6, 6: 2}, {1: 3, 3: 4, 5: 8, 6: 2}, {2: 4, 3: 2, 6: 3}, {4: 2, 5: 4, 6: 3}])
    GM4G = Inst(4, 7, [{0: 3, 2: 6, 5: 2, 6: 10}, {1: 1, 4: 6, 5: 8, 6: 4}, {2: 3, 3: 6, 5: 8, 6: 4},
                       {3: 6, 4: 3, 5: 4, 6: 8}])
    stuck = [('GM4-E', GM4E, [{0, 4}, {1, 3}, {2}, {5}]), ('GM4-G', GM4G, [{0, 2}, {1, 4}, {5}, {6}])]
    for name, own in (('S(3,3)', False), ("S'(3,3)", True)):
        I, Xs, P, src, ch = build(3, 3, own=own); stuck.append((name, I, Xs))
    for name, I, Xs in stuck:
        assert efx0(I, Xs) and pool_ok(I, Xs)
        for copies in (2, 3):
            U, X = dump([(I, [set(B) for B in Xs]) for _ in range(copies)])
            print('%d copies of %s (each stranding %d): complete EFX0 by the recipe: %s' % (
                copies, name, len(pool_of(I, Xs)), efx0(U, X)), flush=True)
            assert efx0(U, X)
    for k in sorted(C):
        print(k, C[k])
    assert all(('False' not in k) for k in C)
    print('all checks passed')
