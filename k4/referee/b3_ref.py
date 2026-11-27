#!/usr/bin/env python3
"""Referee check of base-phantom's Lemma B3 (k4/base_phantom.md §5.1 at 172e8568): at a state reached from a two-move
start by admissible rounds, any allocation X of the present goods to the present agents obtained by at most one
official move (k4/sdc.md §29, my cert_ref.moves on the present instance) and a one-absorber completion that is EFX0
among the present agents and threatens no phantom at its threshold is, with every T, raw EFX0 in I. Own code
(basephantom_ref's rounds, cert_ref's moves and EFX0). Mutations: rounds without (L*), or without (P2)."""
import itertools, json, gzip, sys, random
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, efx0, rel, mk, moves
from oc1hall_ref import threatened
import basephantom_ref as BP

MUT = None

def rounds_mut(v, S, present, goods, phantoms):
    """basephantom_ref.rounds with (L*) or (P2) optionally dropped."""
    sets_ = list(BP.settlements(v, S, present, goods))
    for r in (1, 2):
        for combo in itertools.combinations(sets_, r):
            ags = [a for _, P, _ in combo for a in P]; Ts = [g for _, _, T in combo for g in T]
            if len(ags) != len(set(ags)) or len(Ts) != len(set(Ts)):
                continue
            new = [set(s) for s in S]
            for k, P, T in combo:
                for i in range(1, len(P)):
                    new[P[i]] = set(S[P[i - 1]])
                new[k] = set(T)
            if MUT != "noLstar" and any(threatened(v, a, T, val(v, a, new[a])) for k, _, T in combo for a in present if a != k):
                continue
            if MUT != "noP2" and any(threatened(v, f, T, tf) for _, _, T in combo for f, tf in phantoms):
                continue
            K = {k for k, _, _ in combo}; pres2 = present - K; goods2 = goods - set(Ts)
            if any(len(new[a]) != 1 for a in pres2):
                continue
            from rsd_ref import sd_sub
            if pres2 and not any(all(sd_sub(v, o, pres2, goods2)[a] == next(iter(new[a])) for a in pres2)
                                 for o in itertools.permutations(sorted(pres2))):
                continue
            yield new, pres2, goods2, phantoms + [(k, val(v, k, T)) for k, _, T in combo]

def lift_tests(v, S, present, goods, phantoms, c):
    pa = sorted(present); pg = sorted(goods); n = len(v)
    vm = [[v[a][g] for g in pg] for a in pa]
    gi = {g: i for i, g in enumerate(pg)}
    Bm = [{gi[g] for g in S[a]} for a in pa]
    states = [Bm] + moves(vm, Bm)
    for Bs in states:
        Jm = sorted(set(range(len(pg))) - set().union(*Bs))
        for own in range(len(pa)):
            others = [i for i in range(len(pa)) if i != own]
            def rec(i, X, used):
                if i == len(Jm):
                    yield [set(x) for x in X]; return
                g = Jm[i]
                X[own].add(g); yield from rec(i + 1, X, used); X[own].discard(g)
                for a in others:
                    if a not in used:
                        X[a].add(g); yield from rec(i + 1, X, used | {a}); X[a].discard(g)
            for Xm in rec(0, [set(b) for b in Bs], frozenset()):
                if not efx0(vm, Xm):
                    continue
                X = [set(s) for s in S]
                for i, a in enumerate(pa):
                    X[a] = {pg[g] for g in Xm[i]}
                if any(threatened(v, f, X[a], tf) for f, tf in phantoms for a in pa):
                    continue
                c["hyp_cases"] += 1; c[f"hyp_cases_{len(phantoms)}_phantoms"] += 1
                c["LIFT_VIOLATION"] += not efx0(v, X)

def job(args):
    sets, vals, picks = args
    v = mk(sets, vals); n = len(v); m = len(v[0]); c = Counter(); seen = set()
    def walk(S, present, goods, phantoms, depth):
        key = (tuple(map(frozenset, S)), frozenset(present), tuple(phantoms))
        if key in seen:
            return
        seen.add(key)
        if phantoms:
            c["states"] += 1; lift_tests(v, S, present, goods, phantoms, c)
        if depth == 0:
            return
        for S2, p2, g2, ph2 in rounds_mut(v, S, present, goods, phantoms):
            walk(S2, p2, g2, ph2, depth - 1)
    walk([{y} for y in picks], set(range(n)), set(range(m)), [], 2)
    return c

def main(path, N, seed, procs):
    d = json.load(gzip.open(path)); rows = [(H["sets"], s["vals"], s["picks"]) for H in d["hypergraphs"] for s in H["starts"]]
    rng = random.Random(seed); sample = rng.sample(rows, N)
    c = Counter(starts=N)
    with Pool(procs, initializer=_init, initargs=(MUT,)) as pool:
        for r in pool.imap_unordered(job, sample, chunksize=5):
            c.update(r)
    print(json.dumps(dict(source=f"Lemma B3 lift, n = 4 export sample N={N} seed={seed} mutation={MUT}", **dict(sorted(c.items())))))

def _init(m):
    global MUT
    MUT = m

if __name__ == "__main__":
    MUT = None if sys.argv[5] == "none" else sys.argv[5]
    main(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
