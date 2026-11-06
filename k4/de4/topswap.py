"""Lemma 27 (the top swap; k4/de4.md §10.4, ledger K4.DE4V3R.LP) on double clashes. EVIDENCE for the written proof.

Top swap: a lower-pair holder u takes its top a_u from the agent t holding it alone, and t takes the leftover good j
just below a_u in its own ranking. The level sum is unchanged and there is one lower-pair holder fewer; Lemma R's
repair steps (a lower-pair holder whose b is leftover takes it alone) keep the level sum and lower the number of
lower-pair holders. So where the swap is valid ((V1), (V2)), the state is not a maximum of the lower-pair order. The
proof shows that the swap is valid unless t threatens a triple {b_y, c_y, d_y} with v_t(j); this script checks the
whole statement by brute force on every (V3)-valid (H) state with a double clash (dc_local.roles), and says which
hypothesis fails where no swap applies.

    python3 k4/de4/topswap.py SOURCE PER JOBS SEED       (SOURCE as in refine.py)"""
import sys, os, json, collections, multiprocessing as mp, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import refine as RF
CD = RF.CD; CT = CD.CT; T = CD.T; S = CD.S
from de4lib import leftover, wanted_goods


def roles(I, Y, J, W):
    arcs = CD.graph(I, Y, J, W)
    for c in CD.cycles(I, arcs, I.n):
        if not CD.f2_clash_only(I, Y, J, W, c):
            continue
        lp = [a for a in c if not CT.frozen(Y, a[0], W) and S.types(I, a[0], list(Y[a[0]])) == 'LP']
        if len(lp) < 2:
            continue
        if set(lp[0][2]) & set(lp[1][2]) & J:
            return [a[0] for a in lp]
    return None


def swap(I, Y, J, u):
    """the top swap for u: (status, Z or None)"""
    a = I.ranked(u)[0]
    t = next((x for x in range(I.n) if list(Y[x]) == [a]), None)
    if t is None:
        return 'a_u not held alone', None
    r = I.ranked(t)
    k = r.index(a)
    if k + 1 >= len(r):
        return 'a_u is the last good of t', None
    j = r[k + 1]
    if j not in J:
        return 'the good of t below a_u is held', None
    Z = [list(A) for A in Y]; Z[u] = [a]; Z[t] = [j]
    if not CD.valid(I, Z):
        trip = any(len(Y[y]) >= 3 and I.theta(t, list(Y[y])) > I.v[t][j] for y in range(I.n) if y not in (u, t))
        return 'invalid (%s)' % ('t threatens a triple' if trip else 'OTHER: the proof is wrong'), None
    if T.phi(I, Z) != T.phi(I, Y) or RF.nlp(I, Z) != RF.nlp(I, Y) - 1:
        return 'LEVELS: the proof is wrong', None
    return 'valid', Z


def repair(I, Z):
    """Lemma R: while some lower-pair holder's b is leftover, it takes b alone"""
    while True:
        held = set(g for A in Z for g in A)
        w = next((w for w in range(I.n) if S.types(I, w, Z[w]) == 'LP' and I.ranked(w)[1] not in held), None)
        if w is None:
            return Z
        Z = [list(A) for A in Z]; Z[w] = [I.ranked(w)[1]]


def analyse(I, C, ex, tag):
    All, ph, P = CT.states(I)
    C['instances'] += 1
    for Y, p in zip(All, ph):
        if not T.v3ok(I, Y):
            continue
        J = set(leftover(I, Y))
        if not J:
            continue
        W = set(wanted_goods(I, Y))
        if not CD.H(I, Y, J, W):
            continue
        us = roles(I, Y, J, W)
        if us is None:
            continue
        C['double-clash (V3)-valid (H) states'] += 1
        st = [swap(I, Y, J, u) for u in us]
        for s, _ in st:
            C['  swap for one lower-pair holder: ' + s] += 1
        ok = [Z for s, Z in st if Z is not None]
        if ok:
            Z = repair(I, ok[0])
            good = CD.valid(I, Z) and T.v3ok(I, Z) and T.phi(I, Z) >= T.phi(I, Y) and RF.nlp(I, Z) < RF.nlp(I, Y)
            C['  some swap valid; after Lemma R: (V3)-valid, level sum kept, fewer lower pairs: %s' % good] += 1
        else:
            C['  NO SWAP APPLIES (level sum %s Phi*)' % ('=' if p == P else '<')] += 1
            ex.append((tag, I.sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)], [list(A) for A in Y],
                       [s for s, _ in st]))


RF.analyse = analyse

if __name__ == '__main__':
    src, per, jobs, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    print('$ python3 k4/de4/topswap.py', ' '.join(sys.argv[1:]))
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
