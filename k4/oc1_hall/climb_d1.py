"""Adversarial hill-climb against Conjecture D1-LONG (k4/oc1_hall.md §21).  Objective of a profile: over every order
whose picks have exactly one dangerous agent k and no one-absorber completion (SAT, oc_absorb.extends_A), the least
number of pairs (longest canonical chain from k, inclusion-minimal improving H_0) after which k owns an S* completion;
then the number of such starts (more is better); (99, 0) if there is none.  Minimized; 0 = a counterexample to
D1-LONG, which is then re-tested against ED-MIN over every canonical chain, ED-ANY (d1_rules.py: any ED chain, any
improving H_0, owner k or x_t) and OC1 (any de_free move, then a one-absorber completion), and whether its picks form
a maximum matching.  Starts: logged profiles with N agents that have such a start, then random ones (sdc_climb.start).
A move that leaves no hard start with |D| = 1 is never accepted.

    python3 k4/oc1_hall/climb_d1.py SEED N STEPS ROUNDS
"""
import sys, os, json, random, time, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks
from chain_shapes import s_star_owners
from greedy_rules import canonical_paths
from d1_subcases import analyse
from d1_rules import ed_paths, apply, subsets
from max_matching import nu
from sdclib import Enc
from oc_absorb import extends_A
import de_free as DF
from sdc_climb import mutate, start
DF.CHAIN_ONLY = False


def chains(I, P, base, k):
    """{path: [comp or None for each minimal improving H_0]} over canonical chains from k with an unfrozen head"""
    out = {}; Y = P.Y
    for path in canonical_paths(I, P, k):
        xt = path[-1]
        if xt in P.F: continue
        pool = [g for g in P.J if g in I.R[k]] + ([Y[xt]] if Y[xt] is not None and Y[xt] in I.R[k] else [])
        imp = [H for r in range(1, len(pool) + 1) for H in itertools.combinations(pool, r) if I.val(k, H) > P.pv[k]]
        out[path] = [analyse(I, P, base, k, path, H0)[1] for H0 in imp if not any(set(K) < set(H0) for K in imp)]
    return out


def objective(sets, vals):
    m = 1 + max(max(s) for s in sets); I = Inst(sets, vals, m); E = Enc(sets, vals, m); res = {}
    for od in itertools.permutations(range(I.n)):
        Y = picks(I, od)
        if Y in res: continue
        P = Picks(I, Y); res[Y] = None
        if len(P.D) != 1: continue
        base = base_of_picks(I, Y)
        if extends_A(E, base, 1): continue
        ch = chains(I, P, base, P.D[0])
        if not ch: res[Y] = 0; continue
        L = max(len(p) for p in ch)
        res[Y] = sum(1 for p, cs in ch.items() if len(p) == L for c in cs if c is not None)
    hard = [c for c in res.values() if c is not None]
    if not hard: return (99, 0), None
    lo = min(hard)
    return (lo, -len(hard)), [Y for Y, c in res.items() if c == lo][0]


def retest(sets, vals, Y):
    m = 1 + max(max(s) for s in sets); I = Inst(sets, vals, m); E = Enc(sets, vals, m)
    P = Picks(I, Y); base = base_of_picks(I, Y); k = P.D[0]
    edmin = any(c is not None for cs in chains(I, P, base, k).values() for c in cs)
    edany = False
    for path in ed_paths(I, P, k, I.n):
        xt = path[-1]
        pool0 = [g for g in P.J if g in I.R[k]] + ([Y[xt]] if Y[xt] is not None and Y[xt] in I.R[k] else [])
        for H0 in subsets(pool0):
            if not H0 or I.val(k, H0) <= P.pv[k]: continue
            rest = [g for g in P.J if g not in H0 and g in I.R[xt]]
            for Ht in subsets(rest):
                if I.val(xt, [Y[path[-2]]] + list(Ht)) <= P.pv[xt]: continue
                ow = s_star_owners(I, apply(I, P, base, path, H0, Ht))
                if k in ow or xt in ow: edany = True; break
            if edany: break
        if edany: break
    oc1 = any(extends_A(E, b2, 1) for b2 in DF.moves(E, base))
    return {'ED-MIN (any canonical chain)': edmin, 'ED-ANY': edany, 'OC1 (one move)': oc1,
            'maximum matching': sum(1 for y in Y if y is not None) == nu(I)}


if __name__ == '__main__':
    seed, n, steps, rounds = map(int, sys.argv[1:5]); rng = random.Random(seed); t0 = time.time()
    print('$ python3 k4/oc1_hall/climb_d1.py', *sys.argv[1:], flush=True)
    from min_frozen import load
    pool = [(s_, v_) for _, s_, v_, m_ in load('logs', ['x', 'logs']) if len(s_) == n]
    rng.shuffle(pool); seeds = []
    for s_, v_ in pool:
        if objective(s_, v_)[0][0] < 99: seeds.append((s_, v_))
        if len(seeds) >= rounds: break
    print('seeds with a hard start with |D| = 1:', len(seeds), flush=True)
    for r in range(rounds):
        sets, vals = seeds[r] if r < len(seeds) else start(rng, n); c, Y = objective(sets, vals); best = c
        for s in range(steps):
            mu = mutate(sets, vals, rng)
            if mu is None or len(mu[0]) != n or max(len(x) for x in mu[0]) > 4 or min(len(x) for x in mu[0]) < 1: continue
            c2, Y2 = objective(*mu)
            if c[0] == 99 or (c2[0] < 99 and (c2 <= c or rng.random() < 0.03)):      # never leave the hard region
                (sets, vals), c, Y = mu, c2, Y2; best = min(best, c)
                if c[0] == 0:
                    print('D1-LONG FAILS', json.dumps((sets, vals)), 'picks', Y, retest(sets, vals, Y), flush=True)
                    break
        print('round', r, 'final', c, 'best', best, 'inst', json.dumps((sets, vals)), 'time %.0f' % (time.time() - t0), flush=True)
