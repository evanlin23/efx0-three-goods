#!/usr/bin/env python3
"""Try to break the lemmas of k4/dl2.md §4 on random instances that need not be cores (proof/k4-dl2-k1).

Random strict profiles: n agents with 3 or 4 relevant goods each, strictly balanced (2 v(g) < v(R_i) for every good),
all nonempty subset sums distinct, goods drawn from M = {0, ..., m-1} with every good valued by someone; no core rule
on private goods, connectivity not required. For every min-frozen P with def(P) > 0 (omega >= 1), k4/dl2_classify.py
checks Lemmas 1, 1' (re-bases stay min-frozen with the same needed set), 2, 3 and Corollaries 4, 5 (conclusions asserted
against the exact deficits); this script adds Lemma 1' for trades and Lemma 6 for role swaps with and without a helper:
every move they allow must be a min-frozen P' with the same needed set and the predicted frozen agents; and Lemma 7
at every min-frozen P (z counted, the deficit bound) for every free x, frozen z and safe bundle it applies to.
usage: python3 k4/dl2_lemma_random.py N_INSTANCES [--seed=S] [--nmax=4] [--mmax=9]
       python3 k4/dl2_lemma_random.py N --catalog=FILE [--every=E]      (the first N records of a catalogue, every E-th)"""
import itertools, os, random, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import dl2_classify as DC
from dl2_classify import PA, M, bits, pc, mask


def rand_agent(rng, goods):
    k = rng.choice((3, 4))
    S = rng.sample(goods, k)
    while True:
        vals = [rng.randint(1, 12) for _ in S]
        sums = [sum(c) for r in range(1, k + 1) for c in itertools.combinations(vals, r)]
        if len(set(sums)) == len(sums) and all(2 * v < sum(vals) for v in vals):
            return S, vals


def rand_inst(rng, nmax, mmax):
    n = rng.randint(2, nmax)
    m = rng.randint(n + 2, min(mmax, 4 * n))
    goods = list(range(m))
    while True:
        ag = [rand_agent(rng, goods) for _ in range(n)]
        if set(g for S, _ in ag for g in S) == set(goods): break
    return M.Inst([S for S, _ in ag], [v for _, v in ag], m)


def check_swaps(I, P, PAs):
    """Lemma 1' (trades) and Lemma 6 (role swaps, at most one helper): predicted min-frozen P' with the same 𝒩"""
    n = I.n; N = P.NA; cnt = 0
    def admissible(i, B): return not (I.needs(i, B) & ~N)
    def bases_in(i, G):
        return [mask(c) for k in range(3) for c in itertools.combinations(list(bits(G & I.R[i])), k)]
    for y, w in itertools.combinations(P.free, 2):               # trades
        G = P.J | P.Bs[y] | P.Bs[w]
        for By in bases_in(y, G):
            if not admissible(y, By): continue
            for Bw in bases_in(w, G & ~By):
                if not admissible(w, Bw) or (By == P.Bs[y] and Bw == P.Bs[w]): continue
                b = list(P.Bs); b[y] = By; b[w] = Bw; b = tuple(b)
                assert b in PAs and PAs[b].NA == N and PAs[b].frozen == P.frozen, ('Lemma 1prime', P.Bs, b)
                cnt += 1
    for x in range(n):
        if not P.frozen[x]: continue
        g = P.Bs[x]
        for z in P.free:
            if not (I.R[z] & g) or I.needs(z, g) & ~N: continue
            for h in [None] + [h for h in P.free if h != z]:
                G = P.J | P.Bs[z] | (P.Bs[h] if h is not None else 0)
                for A in bases_in(x, G):
                    if not admissible(x, A): continue
                    for Bh in (bases_in(h, G & ~A) if h is not None else [None]):
                        if Bh is not None and not admissible(h, Bh): continue
                        b = list(P.Bs); b[x] = A; b[z] = g
                        if h is not None: b[h] = Bh
                        b = tuple(b)
                        F2 = list(P.frozen); F2[x] = False; F2[z] = True
                        assert b in PAs and PAs[b].NA == N and PAs[b].frozen == F2, ('Lemma 6', P.Bs, b)
                        cnt += 1
    return cnt


def check_lemma7(I, P, dP):
    """Lemma 7 at a min-frozen P (here playing P'): x free, z frozen on g ∈ R_x, g needed by nobody but x; every safe
    bundle Z of x with v_x(Z) > v_x(g) counts z, and def(P) <= omega + 1 - |Z|"""
    cnt = 0
    omega = pc(P.J) - P.S
    for z in range(I.n):
        if not P.frozen[z]: continue
        g = P.Bs[z]
        for x in P.free:
            if not (I.R[x] & g): continue
            if any(P.N[i] & g for i in range(I.n) if i != x): continue
            vg = I.val(x, g)
            rest = list(bits(P.J))
            for k in range(len(rest) + 1):
                for K in itertools.combinations(rest, k):
                    Z = P.Bs[x] | mask(K)
                    if I.val(x, Z) <= vg or not P.safe(x, Z): continue
                    assert z in DC.counted(P, x, Z), ('Lemma 7: z not counted', P.Bs, x, z, Z)
                    assert dP <= omega + 1 - pc(Z), ('Lemma 7: deficit bound', P.Bs, x, z, Z, dP)
                    cnt += 1
    return cnt


def main(argv):
    N = int(argv[0]) if argv else 200
    opt = dict(a[2:].split('=', 1) for a in argv[1:] if a.startswith('--'))
    rng = random.Random(int(opt.get('seed', 1)))
    nmax, mmax = int(opt.get('nmax', 4)), int(opt.get('mmax', 9))
    print('# command: python3 k4/dl2_lemma_random.py ' + ' '.join(argv), flush=True)
    stats = {'instances': 0, 'omega>=1': 0, 'states': 0, 'L2': 0, 'L2o': 0, 'L3': 0, 'C4': 0, 'C5': 0, 'moves16': 0, 'lemma7': 0}
    if 'catalog' in opt:                          # catalogue profiles instead of random instances (cores)
        import gzip, json
        recs0 = json.load(gzip.open(opt['catalog'], 'rt'))['records'][::int(opt.get('every', 1))][:N]
        source = [M.Inst(r['core']['sets'], r['vals'], r['core']['m']) for r in recs0]
    else:
        source = (rand_inst(rng, nmax, mmax) for _ in range(N))
    for I in source:
        stats['instances'] += 1
        d = {'sets': I.sets, 'vals': [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)], 'm': I.m}
        recs, info = DC.analyze(d)                 # asserts Lemmas 1-3 and Corollaries 4-5 at every def > 0 state
        if info['omega'] < 1: continue
        stats['omega>=1'] += 1
        I.preallocs()
        mp = [Bs for Bs, NA in I.minP]
        PAs = {Bs: PA(I, Bs) for Bs in mp}
        for Bs in mp:
            stats['moves16'] += check_swaps(I, PAs[Bs], PAs)
            dP, _ = PAs[Bs].deficit()
            stats['lemma7'] += check_lemma7(I, PAs[Bs], dP)
        for r in recs:
            stats['states'] += 1
            for k in ('L2', 'L2o', 'L3', 'C4', 'C5'):
                stats[k] += k in r['lemmas']
    print('no violation; ' + ', '.join('%s %d' % kv for kv in stats.items()), flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
