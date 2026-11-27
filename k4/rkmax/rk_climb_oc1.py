"""Adversarial climb against RKMAX itself (k4/rkmax.md §7): seeds are OC1-failing maximum-matching starts Y of a failure
export (n = 5).  A move changes one value of one agent (keeping strict, balanced values); it is kept only if Y stays
a Pareto-optimal maximum matching at which OC1 FAILS (rklib).  Objective (minimized): the number of maximum matchings
with a larger sigma.  Reaching 0 is a counterexample to RKMAX (and to RKDOM's sigma form); the script then re-checks it
with the independent checker k4/sdc/oc1_mc2_rand.Inst.check.  Also tracks rank dominance (RKDOM).
    python3 rk_climb_oc1.py EXPORT SEEDS STEPS SEED"""
import sys, os, gzip, json, random, collections, time, multiprocessing as mp
from rklib import Prof
from rk_climb import strict_balanced
from rk_dominance import dom
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')


def state(sets, vals, Y):
    P = Prof(sets, vals); nu, mm = P.max_matchings()
    if sum(g is not None for g in Y) != nu or not P.pareto_optimal(Y): return None
    if P.oc1(Y) != 'F': return None
    sY = P.sigma(Y); rY = P.ranks(Y)
    nb = sum(1 for M in mm if P.sigma(M) > sY); nd = sum(1 for M in mm if dom(P.ranks(M), rY))
    return (nb, nd), P


def climb(args):
    sets, vals, Y, steps, seed = args
    rng = random.Random(seed); vals = [list(x) for x in vals]; cur = state(sets, vals, Y)
    if cur is None: return {'lost': True}
    best = cur[0]; bestd = cur[0][1]
    for _ in range(steps):
        i = rng.randrange(len(sets)); g = rng.randrange(len(sets[i]))
        nv = [list(x) for x in vals]; nv[i][g] = rng.randint(1, 40)
        if not strict_balanced(nv[i]): continue
        r = state(sets, nv, Y)
        if r is None: continue
        if r[0] <= cur[0] or rng.random() < 0.05:
            vals, cur = nv, r; best = min(best, r[0]); bestd = min(bestd, r[0][1])
            if r[0][0] == 0 or r[0][1] == 0:
                sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc')); from oc1_mc2_rand import Inst
                return {'found': True, 'sets': sets, 'vals': vals, 'picks': Y, 'sigma_better': r[0][0],
                        'dominating': r[0][1], 'independent_check': Inst(sets, vals).check(tuple(Y))}
    return {'found': False, 'best': best, 'best_dominating': bestd}


if __name__ == '__main__':
    F = sys.argv[1]; N, STEPS, SEED = map(int, sys.argv[2:5]); rng = random.Random(SEED)
    print('$ python3 k4/rkmax/rk_climb_oc1.py', os.path.basename(F), *sys.argv[2:], flush=True)
    d = json.load(gzip.open(F))
    starts = [(h['sets'], st['vals'], tuple(st['picks'])) for h in d['hypergraphs'] for st in h['starts']]
    rng.shuffle(starts); starts = starts[:N]
    T = collections.Counter(); t0 = time.time()
    with mp.Pool() as pool:
        for res in pool.imap_unordered(climb, [(a, b, c, STEPS, SEED * 104729 + t) for t, (a, b, c) in enumerate(starts)]):
            if res.get('lost'): T['seed lost'] += 1
            elif res['found']:
                T['FOUND (sigma-better %d, dominating %d, independent: %s)' % (res['sigma_better'], res['dominating'],
                                                                              res['independent_check'])] += 1
                print('FOUND', json.dumps(res), flush=True)
            else:
                T['best (#sigma-better, #dominating) %s; fewest dominating %d' % (res['best'], res['best_dominating'])] += 1
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
