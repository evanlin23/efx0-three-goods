"""RF-PRIV on random strict connected k = 4 cores with a private-top agent: every maximum-matching SD pick vector,
OC1 by the raw checker (k4/sdc/oc1_mc2_rand.py Inst.check). Usage: privtop_random.py N SEED NMIN NMAX"""
import sys, os, random, itertools, collections
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'sdc'))
from oc1_mc2_rand import Inst, gen
from multiprocessing import Pool

def nu(I):
    match = {}
    def aug(a, seen):
        for g in I.R[a]:
            if g in seen: continue
            seen.add(g)
            if g not in match or aug(match[g], seen): match[g] = a; return True
        return False
    return sum(aug(a, set()) for a in range(I.n))

def job(args):
    n, seed = args
    rng = random.Random(seed)
    while True:
        try: sets, vals = gen(n, rng)
        except ValueError: continue          # oc1_mc2_rand.gen occasionally draws fewer shared goods than a degree
        deg = collections.Counter(g for S in sets for g in S)
        pt = [a for a in range(n) if deg[sets[a][vals[a].index(max(vals[a]))]] == 1]
        if pt: break
    I = Inst(sets, vals); N = nu(I)
    C = collections.Counter(); bad = []
    for pk in set(I.sd(o) for o in itertools.permutations(range(n))):
        if sum(x is not None for x in pk) != N: continue
        r = I.check(pk); C[r] += 1
        if r == 'OC1 fails': bad.append((sets, vals, pk))
    return C, bad

if __name__ == '__main__':
    N, seed, nmin, nmax = map(int, sys.argv[1:5])
    T = collections.Counter()
    with Pool(4) as pool:
        for C, bad in pool.imap_unordered(job, [(nmin + i % (nmax - nmin + 1), seed * 100003 + i) for i in range(N)]):
            T.update(C)
            for b in bad: print('RF-PRIV FAILS', b, flush=True)
    print('random private-top cores: %d instances, n = %d..%d' % (N, nmin, nmax))
    for k, x in sorted(T.items()): print('  maximum-matching pick vectors, %-20s %d' % (k, x))
