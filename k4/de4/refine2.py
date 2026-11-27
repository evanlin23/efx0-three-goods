"""Level variants after the refutation of every tie-break of the robust levels (k4/de4.md §10.5; ledger K4.DE4V3R.UT).
EVIDENCE only. Same states as DE4ᵛ³ ((V1), (V2), (V3); holdings: single goods, upper sets, the lower pair); the
level of an upper set that contains the agent's top is changed:
  utop4    upper sets containing the top at level 4 (the top's level), other upper sets 6 if robust else 5,
           lower pair 3, single goods 4/3/2/1;
then the maxima: largest level sum among (V3)-valid states, then fewest lower-pair holders, then value-Pareto.
Counts the maxima that are not completable, and the instances with no completable state of the largest level sum.

    LEVELS=utop4 python3 k4/de4/refine2.py SOURCE PER JOBS SEED       (SOURCE as in refine.py)"""
import sys, os, json, random, collections, multiprocessing as mp, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import refine as RF
CD = RF.CD; CT = CD.CT; T = CD.T; S = CD.S
from de4lib import leftover

LEVELS = os.environ.get('LEVELS', 'utop4')


def level(I, i, A):
    A = list(A)
    if not A:
        return 0
    r = I.ranked(i)
    if len(A) == 1:
        return 4 - r.index(A[0])
    t = S.types(I, i, A)
    if t == 'LP':
        return 3
    # an upper set
    if LEVELS == 'utop4' and r[0] in A:
        return 4
    return 6 if I.val(i, A) >= I.val(i, [g for g in r if g not in A]) else 5


def phi(I, Y):
    return sum(level(I, i, Y[i]) for i in range(I.n))


def analyse(I, C, ex, tag):
    All, _, _ = CT.states(I)
    v3 = [(Y, phi(I, Y)) for Y in All if T.v3ok(I, Y)]
    if not v3:
        return
    P3 = max(p for _, p in v3)
    top = [Y for Y, p in v3 if p == P3]
    Cm = S.Comp(I)
    comp = {}

    def ok(Y):
        k = tuple(tuple(sorted(A)) for A in Y)
        if k not in comp:
            comp[k] = not leftover(I, Y) or Cm.ok([list(A) for A in Y])
        return comp[k]
    C['instances'] += 1
    lpn = [RF.nlp(I, Y) for Y in top]
    mx = RF.pareto_max(I, [Y for Y, k in zip(top, lpn) if k == min(lpn)])
    C['maxima'] += len(mx)
    bad = [Y for Y in mx if not ok(Y)]
    if bad:
        C['NON-COMPLETABLE maxima'] += len(bad)
        C['instances with a non-completable maximum'] += 1
        ex.append((tag, I.sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)], [list(A) for A in bad[0]]))
    if not any(ok(Y) for Y in top):
        C['instances with no completable state of the largest level sum'] += 1


RF.analyse = analyse

if __name__ == '__main__':
    src, per, jobs, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    print('$ LEVELS=%s python3 k4/de4/refine2.py %s' % (LEVELS, ' '.join(sys.argv[1:])))
    if src.startswith('json:'):
        jobs = per
    tot, EX = collections.Counter(), []
    t0 = time.time()
    with mp.Pool(min(jobs, int(os.environ.get('NP', os.cpu_count())))) as pool:
        for C, ex in pool.imap_unordered(RF.job, [(src, per, seed + k) for k in range(jobs)]):
            tot.update(C); EX += ex
    for k in sorted(tot):
        print('%9d  %s' % (tot[k], k))
    for e in EX[:6]:
        print('EX', json.dumps(e))
    print('time %.0f s' % (time.time() - t0))
