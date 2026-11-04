"""The lower-pair tie-break of the robust order (k4/de4.md §10.4; ledger K4.DE4V3R.LP) against the frame of §10:
at each maximum of the order (largest level sum Phi among (V3)-valid states, then fewest lower-pair holders, then
value-Pareto) with leftover goods: completable? does (H) hold, and if not, why (an empty agent, a threat by J alone, a
lateral (V3)-keeping self-upgrade, and of which kind)? With (H): the F2-clash cycles of G, clean or not. EVIDENCE.

    python3 k4/de4/refine_hx.py SOURCE PER JOBS SEED     (SOURCE as in refine.py)"""
import sys, os, json, random, collections, multiprocessing as mp, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import refine as RF
CD = RF.CD; CT = CD.CT; T = CD.T; S = CD.S
from de4lib import leftover, wanted_goods


def lp_maxima(I):
    All, ph, P = CT.states(I)
    v3 = [(Y, p) for Y, p in zip(All, ph) if T.v3ok(I, Y)]
    if not v3:
        return []
    P3 = max(p for _, p in v3)
    top = [Y for Y, p in v3 if p == P3]
    k = [RF.nlp(I, Y) for Y in top]
    return RF.pareto_max(I, [Y for Y, kk in zip(top, k) if kk == min(k)])


def analyse(I, C, ex, tag):
    Cm = None
    C['instances'] += 1
    for Y in lp_maxima(I):
        J = set(leftover(I, Y))
        if not J:
            C['lp-maxima without leftover goods'] += 1
            continue
        Cm = Cm or S.Comp(I)
        comp = Cm.ok([list(A) for A in Y])
        C['lp-maxima with leftover goods: completable %s' % comp] += 1
        W = set(wanted_goods(I, Y))
        why = []
        if not all(Y): why.append('empty agent')
        if any(I.val(x, J) > I.val(x, Y[x]) for x in range(I.n)): why.append('J threat')
        if CT.simple_raise(I, Y, J, W): why.append('SIMPLE RAISE')
        lat, kinds = CT.lateral_v3(I, Y, J, W)
        if lat: why.append('lateral (V3) self-upgrade of ' + '/'.join(kinds))
        if why:
            C['  (H) fails: ' + ', '.join(why)] += 1
            continue
        C['  (H) holds'] += 1
        arcs = CD.graph(I, Y, J, W)
        cyc = [c for c in CD.cycles(I, arcs, I.n) if CD.f2_clash_only(I, Y, J, W, c)]
        unc = [c for c in cyc if len([g for a in c for g in set(a[2]) & J]) != len(set(g for a in c for g in set(a[2]) & J))]
        C['    F2-clash cycles: %d, unclean %d' % (len(cyc) > 0, len(unc) > 0)] += 1
        # clean cycles whose trade keeps the level sum: every taker a free holder of its b taking its lower pair
        flat = [c for c in cyc if c not in unc and all(
            not CT.frozen(Y, a[1], W) and len(Y[a[1]]) == 1 and Y[a[1]][0] == I.ranked(a[1])[1]
            and S.types(I, a[1], list(a[2])) == 'LP' for a in c)]
        if flat:
            C['    clean cycle of b-holders taking lower pairs (level-sum-neutral trade)'] += 1
            ex.append((tag, I.sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)], [list(A) for A in Y], 'flat'))
        if unc or not comp:
            ex.append((tag, I.sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)], [list(A) for A in Y],
                       'unclean' if unc else 'noncompletable'))


RF.analyse = analyse

if __name__ == '__main__':
    src, per, jobs, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    print('$ python3 k4/de4/refine_hx.py', ' '.join(sys.argv[1:]))
    if src.startswith('json:'):
        jobs = per
    tot, EX = collections.Counter(), []
    t0 = time.time()
    with mp.Pool(min(jobs, int(os.environ.get('NP', os.cpu_count())))) as p:
        for C, ex in p.imap_unordered(RF.job, [(src, per, seed + k) for k in range(jobs)]):
            tot.update(C); EX += ex
    for k in sorted(tot):
        print('%9d  %s' % (tot[k], k))
    for e in EX[:8]:
        print('EX', json.dumps(e))
    print('time %.0f s' % (time.time() - t0))
