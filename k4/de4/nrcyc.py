"""Non-robust upper holders on cycles of the arc graph G (k4/de4.md §10.3, Conjecture P2; ledger K4.DE4V3R.C3).
EVIDENCE.

For every (V3)-valid state with (H) (any level sum) in which a free holder o of a non-robust upper set lies on a cycle
of G: is the level sum the largest (P2 says never at a maximum)? Is the cycle clean (pairwise disjoint labels, so
Lemma 18 applies)? The smallest level-raising valid states, with the agents of the cycle named c0 = o, c1 = its
successor, ... (others '?'), in the notation of lpout.py.

    python3 k4/de4/nrcyc.py SOURCE PER JOBS SEED     SOURCE: screen, rand, xhg, hyper"""
import sys, os, json, random, collections, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import claimd as CD, lpout as LO
CT = CD.CT; T = CD.T; S = CD.S
from de4lib import Inst, wanted_goods, leftover
def rsig(I, Y, Z, W, names):
    ch = [i for i in range(I.n) if set(Y[i]) != set(Z[i])]
    holder = {g: i for i in range(I.n) for g in Y[i]}
    parts = []
    for i in ch:
        src = []
        for g in sorted(Z[i], key=lambda g: I.ranked(i).index(g)):
            hh = holder.get(g)
            src.append('abcd'[I.ranked(i).index(g)] + '<' + ('o' if hh == i else 'J' if hh is None else names.get(hh, '?')))
        parts.append('%s:%s>%s[%s](%+d)' % (names.get(i, '?'), LO.lab(I, i, Y[i], W), LO.lab(I, i, Z[i], W), ','.join(src), T.lev(I, i, Z[i]) - T.lev(I, i, Y[i])))
    return ' ; '.join(sorted(parts))
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
        cs = CD.cycles(I, arcs, I.n)
        hit = None
        for c in cs:
            for k, a in enumerate(c):
                o = a[0]
                if not CT.frozen(Y, o, W) and len(Y[o]) >= 2 and T.lev(I, o, Y[o]) == 5:
                    hit = (c, k); break
            if hit: break
        if not hit: continue
        c, k = hit
        lab = [g for a in c for g in set(a[2]) & J]
        clean = len(lab) == len(set(lab))
        C['(H) state with a non-robust upper holder on a cycle: top %s, cycle clean %s' % (p == P, clean)] += 1
        if p == P: ex.append((tag, I.sets, [I.v[i] for i in range(I.n)], [list(A) for A in Y])); continue
        names = {}
        for t, a in enumerate(c): names[a[0]] = 'c%d' % ((t - k) % len(c))
        best = None; sigs = []
        for Z, q in zip(All, ph):
            if q <= p: continue
            m = sum(set(Y[i]) != set(Z[i]) for i in range(I.n))
            if best is None or m < best: best, sigs = m, [rsig(I, Y, Z, W, names)]
            elif m == best: sigs.append(rsig(I, Y, Z, W, names))
        C['  minimal raise size %s (cycle length %d, clean %s)' % (best, len(c), clean)] += 1
        if not clean:
            for s_ in sorted(set(sigs))[:2]: C['    unclean sig %s' % s_] += 1
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
    print('$ python3 k4/de4/nrcyc.py', ' '.join(sys.argv[1:]))
    tot, EX = collections.Counter(), []
    with mp.Pool(int(os.environ.get('NP', 3))) as p:
        for C, ex in p.imap_unordered(job, [(src, per, seed + k) for k in range(jobs)]): tot.update(C); EX += ex
    for k in sorted(tot): print('%7d  %s' % (tot[k], k))
    for e in EX[:6]: print('EX', json.dumps(e))
