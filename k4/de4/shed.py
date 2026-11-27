"""Shed-completability (k4/de4.md §10.5; ledger K4.DE4V3R.SHED, K4.DE4V3R.SHED2). EVIDENCE only.

A state Y is shed-completable if, for some set of agents w holding an upper set that contains w's top a_w, replacing
Y_w by {a_w} (releasing the rest) gives a partial allocation with an EFX0 completion (SHED=top, the default); with
SHED=broad, any agent holding two or more goods may keep any one good of its holding. This is weaker than
completability and still gives an EFX0 allocation. For each instance: the non-completable maxima of the robust order
(largest robust level sum, then value-Pareto) and of the lower-pair order, and which of them are shed-completable.

    python3 k4/de4/shed.py SOURCE PER JOBS SEED       (SOURCE as in refine.py)"""
import sys, os, json, itertools, collections, multiprocessing as mp, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import refine as RF
CD = RF.CD; CT = CD.CT; T = CD.T; S = CD.S
from de4lib import leftover


MODE = os.environ.get('SHED', 'top')


def shed_ok(I, Y, Cm):
    """SHED=top (K4.DE4V3R.SHED): holders of an upper set containing their top may keep the top alone;
    SHED=broad (K4.DE4V3R.SHED2): holders of two or more goods may keep any one good of their holding."""
    if MODE == 'broad':
        cand = [w for w in range(I.n) if len(Y[w]) >= 2]
        choices = {w: list(Y[w]) for w in cand}
    else:
        cand = [w for w in range(I.n) if len(Y[w]) >= 2 and S.types(I, w, list(Y[w])) in ('U', 'UR')
                and I.ranked(w)[0] in Y[w]]
        choices = {w: [I.ranked(w)[0]] for w in cand}
    for k in range(1, len(cand) + 1):
        for ws in itertools.combinations(cand, k):
            for keep in itertools.product(*[choices[w] for w in ws]):
                Z = [list(A) for A in Y]
                for w, g in zip(ws, keep):
                    Z[w] = [g]
                if Cm.ok(Z):
                    return ws, keep
    return None


def analyse(I, C, ex, tag):
    All, ph, P = CT.states(I)
    v3 = [(Y, p) for Y, p in zip(All, ph) if T.v3ok(I, Y)]
    if not v3:
        return
    P3 = max(p for _, p in v3)
    top = [Y for Y, p in v3 if p == P3]
    Cm = S.Comp(I)
    C['instances'] += 1
    lpn = [RF.nlp(I, Y) for Y in top]
    for name, M in (('robust', RF.pareto_max(I, top)),
                    ('lower-pair', RF.pareto_max(I, [Y for Y, k in zip(top, lpn) if k == min(lpn)]))):
        for Y in M:
            if not leftover(I, Y) or Cm.ok([list(A) for A in Y]):
                continue
            ws = shed_ok(I, Y, Cm)
            C['%-10s non-completable maximum: shed-completable %s' % (name, ws is not None)] += 1
            if ws is None:
                ex.append((name, tag, I.sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)], [list(A) for A in Y]))


RF.analyse = analyse

if __name__ == '__main__':
    src, per, jobs, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    print('$ SHED=%s python3 k4/de4/shed.py %s' % (MODE, ' '.join(sys.argv[1:])))
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
