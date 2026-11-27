#!/usr/bin/env python3
"""Referee replay of ksens's N3K5 and N3K5+ (k4/ksens.md §8 on claude/k4-ksens at 1ac11ad): at k = 5, one chain (and
one round) fails already at n = 3. Own code (cert_ref.py: SD, §29 moves incl. the certifier's rings, one-absorber and
free completions, raw EFX0; oc1p_ref.py: the OC1' widened generator); nothing from k4/ksens/ is run or imported. The
instance data are copied from the note.

A round (kgen/rounds.md §1): vertex-disjoint chains applied at once; a chain x_0..x_t (t >= 0): x_0 takes
H_0 ⊆ J ∪ B_{x_t} (t >= 1; its own chain's end only) or adds H_0 ⊆ J (t = 0); x_i takes B_{x_{i-1}} + H_i, H_i ⊆ J;
H sets pairwise disjoint over the whole round; every chain agent strictly gains. Generators: H sets inside the
taker's relevant goods ('strict') or any goods ('wide').
Counts are [states, with a one-absorber completion, with a free completion]; "extra" = not already in the classes before.
"""
import itertools, json, sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, efx0, sd, nu, complete, moves, oc_depth, subsets
from oc1p_ref import oc1p_moves, uniq

def mkfull(sets, vals, m):
    v = [[0] * m for _ in sets]
    for i, (s, x) in enumerate(zip(sets, vals)):
        for g, y in zip(s, x):
            v[i][g] = y
    return v

def rounds(v, B, wide=False):
    """every state one round away from B."""
    n = len(B); m = len(v[0]); J = set(range(m)) - set().union(*B)
    R = [set(range(m)) if wide else {g for g in range(m) if v[i][g] > 0} for i in range(n)]
    out = []
    def chains_of(agents):
        # all sequences (t >= 0) over a subset of agents
        for r in range(1, len(agents) + 1):
            for seq in itertools.permutations(agents, r):
                yield seq
    def place(free_agents, used, nb, any_chain):
        # either stop, or start a new chain with the smallest-index free agent as some member
        if any_chain:
            out.append([set(b) for b in nb])
        rest = sorted(free_agents)
        for r in range(1, len(rest) + 1):
            for seq in itertools.permutations(rest, r):
                if any_chain and min(seq) < any_chain_min[0]:
                    pass
                t = len(seq) - 1
                if t >= 1 and any(not B[x] for x in seq[:-1]):
                    continue
                def rec(i, u, c):
                    if i > t:
                        pool = ((J - u) | (B[seq[-1]] if t >= 1 else set())) & R[seq[0]]
                        for H0 in subsets(pool):
                            if not H0:
                                continue
                            newb = (B[seq[0]] | H0) if t == 0 else set(H0)
                            if val(v, seq[0], newb) > val(v, seq[0], B[seq[0]]):
                                cc = [set(b) for b in c]; cc[seq[0]] = newb
                                yield u | H0, cc
                        return
                    xi, pr = seq[i], seq[i - 1]
                    for Hi in subsets((J - u) & R[xi]):
                        if val(v, xi, B[pr] | Hi) > val(v, xi, B[xi]):
                            cc = [set(b) for b in c]; cc[xi] = B[pr] | Hi
                            yield from rec(i + 1, u | Hi, cc)
                for u2, c2 in rec(1, set(used), nb):
                    place(free_agents - set(seq), u2, c2, True)
    any_chain_min = [0]
    place(set(range(n)), set(), [set(b) for b in B], False)
    return uniq(out)

def report(name, v, order, Y_expected):
    n = len(v); m = len(v[0])
    Y = sd(v, order); B = [{y} for y in Y]
    orders = [o for o in itertools.permutations(range(n)) if sd(v, list(o)) == Y]
    res = dict(instance=name, picks=Y, picks_as_stated=list(Y) == list(Y_expected), orders_giving_picks=len(orders),
               nu=nu(v), relevant_goods=[sum(1 for x in row if x > 0) for row in v],
               picks_one_absorber=complete(v, B) is not None, picks_free=complete(v, B, free=True) is not None)
    K = lambda st: tuple(frozenset(b) for b in st)
    s29 = uniq(moves(v, B))
    rings = [st for st in uniq(moves(v, B, rings=True)) if K(st) not in {K(x) for x in s29}]
    for gen, wide in (("strict", False), ("wide", True)):
        p1 = [st for st in uniq(oc1p_moves(v, B, wide)) if K(st) not in {K(x) for x in s29 + rings}]
        rd = rounds(v, B, wide)
        for cls, sts in (("sec29_chains_and_additions", s29), ("certifier_rings_extra", rings), ("OC1p_extra", p1), ("rounds", rd)):
            if gen == "wide" and cls in ("sec29_chains_and_additions", "certifier_rings_extra"):
                continue
            res[f"{cls}_{gen}"] = [len(sts), sum(complete(v, st) is not None for st in sts),
                                   sum(complete(v, st, free=True) is not None for st in sts)]
        if gen == "strict":
            res["OC1p_extra_completing_states"] = [[sorted(b) for b in st] for st in p1 if complete(v, st) is not None]
    res["oc_depth_sec29_one_absorber"] = oc_depth(v, Y, 2)
    two_rounds = 0
    for s1 in rounds(v, B):
        if any(complete(v, s2) is not None for s2 in rounds(v, s1)):
            two_rounds += 1
    res["first_rounds_followed_by_a_repairing_round"] = two_rounds
    print(json.dumps(res))

if __name__ == "__main__":
    SETS = [[0, 2, 3, 4, 5], [1, 2, 3, 4, 5], [1, 4, 5]]
    VALS = [[3, 22, 23, 38, 43], [15, 17, 27, 40, 43], [1, 2, 4]]
    m = 6
    v = mkfull(SETS, VALS, m)
    report("N3K5", v, [1, 0, 2], [4, 5, 1])
    w = [[100 * x for x in row] for row in v]; c = 0
    for i in range(3):
        for g in range(m):
            if w[i][g] == 0:
                c += 1; w[i][g] = c
    print(json.dumps(dict(N3K5plus_values=w)))
    report("N3K5+", w, [1, 0, 2], [4, 5, 1])
