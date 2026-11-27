"""Locality of the raises for out-arcs of lower-pair holders (k4/de4.md §10.3; ledger K4.DE4V3R.C3). EVIDENCE.

For every out-arc (x, D) of a free lower-pair holder u at a (V3)-valid (H) state (any level sum), the smallest raise
(a valid state of larger level sum) that changes only agents among u, x, the holder h of a_u and the holder w of b_u.
'None' means every raise changes some other agent.

    python3 k4/de4/lploc.py SOURCE PER JOBS SEED     SOURCE: screen, rand, xhg, hyper"""
import sys, os, json, random, collections, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import claimd as CD, lpout as LO
CT = CD.CT; T = CD.T; S = CD.S
from de4lib import Inst, wanted_goods, leftover
def analyse(I, C, ex, tag):
    All, ph, P = CT.states(I)
    if not All: return
    for Y, p in zip(All, ph):
        if not T.v3ok(I, Y): continue
        J = set(leftover(I, Y))
        if not J: continue
        W = set(wanted_goods(I, Y))
        if not CD.H(I, Y, J, W): continue
        arcs = CD.graph(I, Y, J, W)
        lps = [a for a in arcs if not CT.frozen(Y, a[0], W) and S.types(I, a[0], list(Y[a[0]])) == 'LP']
        for u, x, D in lps:
            r = I.ranked(u)
            h = next(k for k in range(I.n) if r[0] in Y[k]); w = next(k for k in range(I.n) if r[1] in Y[k])
            loc = {u, x, h, w}
            best = None; sig = None
            for Z, q in zip(All, ph):
                if q <= p: continue
                ch = {i for i in range(I.n) if set(Y[i]) != set(Z[i])}
                if ch <= loc and (best is None or len(ch) < best):
                    best, sig = len(ch), LO.role_sig(I, Y, Z, W, u, x, D)
            role = 'h' if x == h else 'w' if x == w else 'other'
            C['LP out-arc, taker %s: local raise among {u,x,h,w} %s' % (role, best)] += 1
            if best is None and len(ex) < 8: ex.append((tag, I.sets, [I.v[i] for i in range(I.n)], [list(A) for A in Y], u, x, list(D)))
            if sig and role == 'other': C['   other-taker sig %s' % sig] += 1
def job(args):
    src, per, seed = args
    rng = random.Random(seed); C = collections.Counter(); ex = []
    if src == 'screen':
        for name, I in S.screen_set(): analyse(I, C, ex, name)
        return C, ex
    for _ in range(per):
        if src == 'rand': I = CD.random_r1(rng)
        else:
            cores = CD.XHG if src == 'xhg' else json.load(open(os.path.join(ROOT, 'results/k4_de4/stuck_hypergraphs.json')))['hypergraphs']
            s = rng.choice(cores); I = Inst(s, CD.random_profile(s, rng))
        analyse(I, C, ex, src)
    return C, ex
if __name__ == '__main__':
    src, per, jobs, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    print('$ python3 k4/de4/lploc.py', ' '.join(sys.argv[1:]))
    tot, EX = collections.Counter(), []
    with mp.Pool(int(os.environ.get('NP', 3))) as p:
        for C, ex in p.imap_unordered(job, [(src, per, seed + k) for k in range(jobs)]): tot.update(C); EX += ex
    for k in sorted(tot): print('%7d  %s' % (tot[k], k))
    for e in EX[:8]: print('EX', json.dumps(e))
