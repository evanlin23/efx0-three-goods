"""What happens to the dangerous agents in the repairing moves (k4/RFMIN.md §6, Conjecture RF-PRIV').

At every RF-PRIV gap start (random private-top cores; the generator and seeds of privtop_gap.py), every official move
(Inst.moves) after which ABS' holds for f is classified by the fate of each d in D_full (frozen agents valuing the junk
above their pick):
  junk     d's new bundle is junk only (d starts the chain, H0 inside the junk);
  pick+    d's new bundle holds a pick (its wanter's or the head's) together with junk;
  better   d's new bundle is a single better pick;
  freed    d keeps its pick and is a receiver after the move (every wanter of Y_d got something it prefers);
  kept     d keeps its pick, is still frozen, and the move took enough of its junk.
For each start, the least of the fate sets {junk, freed} < {.., pick+} < {.., better} < {.., kept} that some ABS' move
stays inside is reported.
Usage: privtop_fates.py N SEED NMIN NMAX"""
import sys, os, random, itertools, collections, json
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'sdc'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from oc1_mc2_rand import Inst, gen
from privtop_random import nu
from privtop_absp import absp
from multiprocessing import Pool


def fate(I, base, st, d, J):
    if sorted(st[d]) != sorted(base[d]):
        if all(g in J for g in st[d]): return 'junk'
        if any(g in J for g in st[d]): return 'pick+'
        return 'better'
    b = [I.V(i, st[i]) for i in range(I.n)]
    wanted = any(i != d and I.V(i, st[d]) > b[i] for i in range(I.n))
    return 'kept' if wanted else 'freed'


def job(args):
    n, seed = args
    rng = random.Random(seed)
    while True:
        try: sets, vals = gen(n, rng)
        except ValueError: continue
        deg = collections.Counter(g for S in sets for g in S)
        pt = [a for a in range(n) if deg[sets[a][vals[a].index(max(vals[a]))]] == 1]
        if pt: break
    I = Inst(sets, vals); N = nu(I); f = pt[0]
    C = collections.Counter()
    for pk in set(I.sd(o) for o in itertools.permutations(range(n))):
        if sum(x is not None for x in pk) != N: continue
        base = [[g] if g is not None else [] for g in pk]
        if absp(I, base, f)[0] == 'ok' or I.one_absorber(base): continue
        J = set(range(I.m)) - {g for g in pk if g is not None}
        p = [I.V(i, base[i]) for i in range(n)]
        D = [a for a in range(n) if pk[a] is not None and I.V(a, J) > p[a]
             and any(i != a and I.v[i].get(pk[a], 0) > p[i] for i in range(n))]
        C['gap starts, |D_full| = %d' % len(D)] += 1
        vecs = set()
        for st in I.moves(base):
            st = [list(x) for x in st]
            why, X = absp(I, st, f)
            if why != 'ok': continue
            assert I.efx0(X)
            vecs.add(tuple(sorted(fate(I, base, st, d, J) for d in D)))
        assert vecs, ('RF-PRIV\' fails', sets, vals, pk)
        for v in vecs: C['  |D_full| = %d: some ABS\' move with fates %s' % (len(D), '+'.join(v))] += 1
        kinds = set(x for v in vecs for x in v)
        if any('kept' not in v for v in vecs): C['  some ABS\' move in which every dangerous agent moves or is freed'] += 1
        else: C['  every ABS\' move keeps some dangerous agent frozen on its pick'] += 1
        if any(set(v) <= {'junk', 'freed'} for v in vecs): C['  some ABS\' move with fates in {junk, freed} only'] += 1
        if any(set(v) <= {'junk', 'pick+', 'freed'} for v in vecs): C['  some ABS\' move with fates in {junk, pick+, freed}'] += 1
        lev = [('junk', 'freed'), ('junk', 'freed', 'pick+'), ('junk', 'freed', 'pick+', 'better'),
               ('junk', 'freed', 'pick+', 'better', 'kept')]
        L = next(k for k, S in enumerate(lev) if any(set(v) <= set(S) for v in vecs))
        C['|D_full| = %d: least fate set that some ABS\' move stays inside: {%s}' % (len(D), ', '.join(lev[L]))] += 1
    return C


if __name__ == '__main__':
    N, seed, nmin, nmax = map(int, sys.argv[1:5])
    T = collections.Counter()
    with Pool(4) as pool:
        for C in pool.imap_unordered(job, [(nmin + i % (nmax - nmin + 1), seed * 1000003 + i) for i in range(N)]):
            T.update(C)
    print('fates of the dangerous agents in the ABS\' moves at RF-PRIV gap starts: %d cores, n = %d..%d, seed %d' % (
        N, nmin, nmax, seed))
    for k, x in sorted(T.items()): print('  %-76s %d' % (k, x))
