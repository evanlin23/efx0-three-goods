"""Lemma 31 (the keep-own swap; k4/de4.md §10.4; ledger K4.DE4V3R.L27). EVIDENCE for the written proof.

On every (V3)-valid state: for each holder u of its lower pair {c_u, d_u} such that {b_u, c_u} is an upper set of u, and
whose b_u is held by an agent w in the pair {b_u, a_w} (w's top and b_u): u takes {b_u, c_u}, w keeps {a_w}, d_u is
released. Claimed: valid unless w threatens a holding of three or more goods with v_w(a_w); level sum not lower; one
lower-pair holder fewer. Any 'CLAIM FAILS' line refutes the written proof.

    python3 k4/de4/keepown.py SOURCE PER JOBS SEED       (SOURCE as in refine.py)"""
import sys, os, json, collections, multiprocessing as mp, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import refine as RF
CD = RF.CD; CT = CD.CT; T = CD.T; S = CD.S
from de4lib import leftover


def analyse(I, C, ex, tag):
    All, ph, P = CT.states(I)
    C['instances'] += 1
    for Y, p in zip(All, ph):
        if not T.v3ok(I, Y):
            continue
        for u in range(I.n):
            if S.types(I, u, list(Y[u])) != 'LP':
                continue
            a, b, c, d = I.ranked(u)
            if not (I.v[u][b] + I.v[u][c] > I.v[u][a]):
                continue
            w = next(x for x in range(I.n) if b in Y[x])
            if len(Y[w]) != 2:
                continue
            q = next(g for g in Y[w] if g != b)
            if q != I.ranked(w)[0]:
                continue
            trip = any(len(Y[y]) >= 3 and I.theta(w, list(Y[y])) > I.v[w][q] for y in range(I.n) if y not in (u, w))
            Z = [list(A) for A in Y]; Z[u] = [b, c]; Z[w] = [q]
            ok = CD.valid(I, Z) and T.phi(I, Z) >= p and RF.nlp(I, Z) == RF.nlp(I, Y) - 1
            where = 'Phi*' if p == P else 'below Phi*'
            if trip:
                C['  w threatens a triple (outside the lemma), %s; swap valid anyway %s' % (where, ok)] += 1
                continue
            C['keep-own swap applies, %s: claim holds %s' % (where, ok)] += 1
            if not ok:
                print('CLAIM FAILS', json.dumps((I.sets, [[I.v[i][x] for x in I.sets[i]] for i in range(I.n)],
                                                    [list(A) for A in Y], Z)), flush=True)


RF.analyse = analyse

if __name__ == '__main__':
    src, per, jobs, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    print('$ python3 k4/de4/keepown.py', ' '.join(sys.argv[1:]))
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
