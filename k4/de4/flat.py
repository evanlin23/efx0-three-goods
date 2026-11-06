"""Flat cycles (k4/de4.md §10.4; ledger K4.DE4V3R.LP): clean F2-clash cycles of G whose trade keeps the level sum (every
taker a free holder of its b taking its lower pair), at every (V3)-valid (H) state of the largest level sum, and below
it. EVIDENCE.      python3 k4/de4/flat.py SOURCE PER JOBS SEED   (SOURCE as in refine.py)"""
import sys, os, json, collections, multiprocessing as mp, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import refine as RF
CD = RF.CD; CT = CD.CT; T = CD.T; S = CD.S
from de4lib import leftover, wanted_goods


def analyse(I, C, ex, tag):
    All, ph, P = CT.states(I)
    v3 = [(Y, p) for Y, p in zip(All, ph) if T.v3ok(I, Y)]
    if not v3:
        return
    P3 = max(p for _, p in v3)
    C['instances'] += 1
    for Y, p in v3:
        J = set(leftover(I, Y))
        if not J:
            continue
        W = set(wanted_goods(I, Y))
        if not CD.H(I, Y, J, W):
            continue
        where = 'Phi*' if p == P3 else 'below Phi*'
        C['(V3)-valid (H) states, %s' % where] += 1
        for c in CD.cycles(I, CD.graph(I, Y, J, W), I.n):
            if not CD.f2_clash_only(I, Y, J, W, c):
                continue
            lab = [g for a in c for g in set(a[2]) & J]
            if len(lab) != len(set(lab)):
                continue
            if all(not CT.frozen(Y, a[1], W) and len(Y[a[1]]) == 1 and Y[a[1]][0] == I.ranked(a[1])[1]
                   and S.types(I, a[1], list(a[2])) == 'LP' for a in c):
                C['  FLAT cycle, %s' % where] += 1
                if len(ex) < 5:
                    ex.append((tag, where, I.sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)],
                               [list(A) for A in Y], c))
                break


RF.analyse = analyse

if __name__ == '__main__':
    src, per, jobs, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    print('$ python3 k4/de4/flat.py', ' '.join(sys.argv[1:]))
    if src.startswith('json:'):
        jobs = per
    tot, EX = collections.Counter(), []
    t0 = time.time()
    with mp.Pool(min(jobs, int(os.environ.get('NP', os.cpu_count())))) as p:
        for C, ex in p.imap_unordered(RF.job, [(src, per, seed + k) for k in range(jobs)]):
            tot.update(C); EX += ex
    for k in sorted(tot):
        print('%9d  %s' % (tot[k], k))
    for e in EX[:5]:
        print('EX', json.dumps(e))
    print('time %.0f s' % (time.time() - t0))
