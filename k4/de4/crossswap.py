"""Lemma 30 (k4/de4.md §10.4; ledger K4.DE4V3R.L27): the cross and lopsided swaps on double clashes. EVIDENCE for the
written proof: on every (V3)-valid (H) state with a double clash (topswap.roles), for each frozen agent t whose
danger set is its pair {c_t, d_t} = {j, g} (j leftover, g in the other lower-pair holder's pair):
  (a) cross swap, when the other frozen agent t' has b_{t'} in a lower pair of the clash and b_{t'} != g:
      u, u' take their tops, t takes {c_t, d_t}, t' takes b_{t'}; claimed: valid, level sum +2 or more;
  (b) lopsided swap, when t' has {c_{t'}, d_{t'}} = {g', j} with g' = c_{t'} in u's pair, j = d_{t'}, and b_{t'}
      held alone: u, u' take their tops, t takes {c_t, d_t}, t' takes c_{t'}; claimed: valid, level sum +1 or more.
Prints the counts; any 'CLAIM FAILS' line refutes the written proof.

    python3 k4/de4/crossswap.py SOURCE PER JOBS SEED       (SOURCE as in refine.py)"""
import sys, os, json, collections, multiprocessing as mp, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import refine as RF
import topswap as TS
CD = RF.CD; CT = CD.CT; T = CD.T; S = CD.S
from de4lib import leftover, wanted_goods


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
        us = TS.roles(I, Y, J, W)
        if us is None:
            continue
        C['double-clash (V3)-valid (H) states'] += 1
        holder = {g: i for i in range(I.n) for g in Y[i]}
        ts = []
        for u in us:
            a = I.ranked(u)[0]
            t = next((x for x in range(I.n) if list(Y[x]) == [a]), None)
            ts.append(t)
        if None in ts or ts[0] == ts[1]:
            continue
        pairs = set(Y[us[0]]) | set(Y[us[1]])
        for k in (0, 1):
            u, t, u2, t2 = us[k], ts[k], us[1 - k], ts[1 - k]
            rt, rt2 = I.ranked(t), I.ranked(t2)
            if len(rt) != 4 or rt[0] != I.ranked(u)[0]:
                continue
            cd = set(rt[2:])
            js = cd & J; gs = cd & set(Y[u2])
            if len(js) != 1 or len(gs) != 1 or I.val(t, list(cd)) <= I.v[t][rt[0]]:
                continue
            g = next(iter(gs))
            bt2 = rt2[1] if len(rt2) >= 2 else None
            claim = None
            if bt2 in pairs and bt2 != g and rt2[0] == I.ranked(u2)[0]:
                claim, new2, gain = 'a', [bt2], 2
            elif (len(rt2) == 4 and rt2[0] == I.ranked(u2)[0] and rt2[3] in J and rt2[3] in js
                  and rt2[2] in Y[u] and any(list(Y[w]) == [bt2] for w in range(I.n))):
                claim, new2, gain = 'b', [rt2[2]], 1
            if claim is None:
                C['  frozen t with danger set {c_t, d_t} = {j, g}: neither (a) nor (b) applies'] += 1
                continue
            Z = [list(A) for A in Y]
            Z[u] = [I.ranked(u)[0]]; Z[u2] = [I.ranked(u2)[0]]; Z[t] = sorted(cd); Z[t2] = new2
            ok = CD.valid(I, Z) and T.phi(I, Z) >= p + gain
            C['  (%s) applies: claim holds %s' % (claim, ok)] += 1
            if not ok:
                print('CLAIM FAILS', claim, json.dumps((I.sets, [[I.v[i][x] for x in I.sets[i]] for i in range(I.n)],
                                                        [list(A) for A in Y], Z)), flush=True)


RF.analyse = analyse

if __name__ == '__main__':
    src, per, jobs, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    print('$ python3 k4/de4/crossswap.py', ' '.join(sys.argv[1:]))
    if src.startswith('json:'):
        jobs = per
    tot = collections.Counter()
    t0 = time.time()
    with mp.Pool(min(jobs, int(os.environ.get('NP', os.cpu_count())))) as pool:
        for C, ex in pool.imap_unordered(RF.job, [(src, per, seed + k) for k in range(jobs)]):
            tot.update(C)
    for k in sorted(tot):
        print('%9d  %s' % (tot[k], k))
    print('time %.0f s' % (time.time() - t0))
