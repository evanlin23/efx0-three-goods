"""Which receiver-first order (k4/ttc.md §14.9): do the promotion rules keep the matching maximum?  A pure matching test
on random k = 4 cores of the K4.MC2 generator (k4/sdc/oc1_mc2_rand.gen), no EFX check.

For random instances and random orders o with a maximum SD outcome Y (as large as a maximum matching of the
acceptability graph), and every receiver u of Y: is the outcome of each rule a maximum matching?  Rules: ROT (u, o - u);
YRMH; YRMH-L and ROT-L (rf_diag.promote_sd).  Also: does some u-first order give a maximum outcome (all (n - 1)!
u-first orders, n <= 8)?  For YRMH-F and ROT-F (rf_diag.feasible_sd): is the outcome maximum, is u first, and is it the
SD outcome of its realized order (the pointer lemma of k4/ttc.md §14.9 says: maximum and u first whenever some u-first
order gives a maximum outcome).  Evidence only.

    python3 k4/ttc/rf_maxcheck.py N_INST SEED NMIN NMAX"""
import sys, os, random, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'sdc')); sys.path.insert(0, HERE)
from oc1_mc2_rand import Inst, gen
from rf_rules import receivers, yrmh
from rf_diag import promote_sd, feasible_sd


def max_matching(I):
    match = {}

    def aug(a, seen):
        for g in I.R[a]:
            if g not in seen:
                seen.add(g)
                if g not in match or aug(match[g], seen):
                    match[g] = a
                    return True
        return False
    return sum(aug(a, set()) for a in range(I.n))


if __name__ == '__main__':
    print('$ python3 k4/ttc/rf_maxcheck.py', *sys.argv[1:], flush=True)
    N, seed, nmin, nmax = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter(); ex = []
    for t in range(N):
        n = rng.randint(nmin, nmax); sets, vals = gen(n, rng); I = Inst(sets, vals); mm = max_matching(I)
        for _ in range(4):
            o = list(range(n)); rng.shuffle(o); Y = I.sd(o)
            if sum(y is not None for y in Y) < mm:
                C['orders with a non-maximum SD outcome (skipped)'] += 1; continue
            for u in receivers(I, Y):
                C['(start, receiver) pairs, n = %d' % n] += 1
                q = [u] + [a for a in o if a != u]
                outs = {'ROT': I.sd(q), 'YRMH': yrmh(I, Y, o, u)[0], 'YRMH-L': promote_sd(I, Y, q)[0],
                        'ROT-L': promote_sd(I, Y, q, eject=False)[0]}
                Zf, ordf = feasible_sd(I, Y, q); Zrf, ordrf = feasible_sd(I, Y, q, eject=False)
                exists = any(sum(z is not None for z in I.sd((u,) + r)) >= mm
                             for r in itertools.permutations([a for a in range(n) if a != u]))
                C['some u-first order gives a maximum outcome' if exists else 'NO u-first order gives a maximum outcome'] += 1
                for rule, (Z, od) in (('YRMH-F', (Zf, ordf)), ('ROT-F', (Zrf, ordrf))):
                    if Z == ('stuck',):
                        C['%s STUCK (%s)' % (rule, 'a maximum u-first outcome exists' if exists else 'none exists')] += 1
                        continue
                    mx = sum(z is not None for z in Z) >= mm; uf = od[0] == u
                    C['%s: maximum %s, u first %s, (a maximum u-first outcome exists: %s)' % (rule, mx, uf, exists)] += 1
                    if Z != I.sd(od):
                        C['%s: ERROR, outcome is not the SD outcome of its realized order' % rule] += 1
                for rule, Z in outs.items():
                    ok = sum(z is not None for z in Z) >= mm
                    C['%s maximum' % rule if ok else '%s NOT maximum' % rule] += 1
                    if not ok and rule == 'YRMH-L' and exists and len(ex) < 3:
                        ex.append({'sets': sets, 'vals': vals, 'o': o, 'Y': Y, 'u': u, 'YRMH-L': Z})
    for k in sorted(C):
        print(k, C[k])
    for e in ex:
        print('YRMH-L not maximum although a maximum u-first outcome exists:', e)
