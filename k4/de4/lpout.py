"""Out-arcs of lower-pair holders (k4/de4.md §10.3; ledger K4.DE4V3R.C3). EVIDENCE.

For every (V3)-valid state with (H) (any level sum) in which a free holder u of its lower pair has an out-arc (x, D) of
the arc graph G: is the level sum the largest (Conjecture P1 says never)? Otherwise, the smallest level-raising valid
states (fewest agents changed), described by the roles of the agents: u, the taker x, the holder h of a_u, the holder
w of b_u, others o. A holding is written in the agent's rank letters (F: frozen, *: robust), each good with its
source (o: own, J: leftover, or the previous holder's role), and the level change.

    python3 k4/de4/lpout.py SOURCE PER JOBS SEED     SOURCE: screen, rand, xhg, hyper"""
import sys, os, json, random, collections, multiprocessing as mp, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import claimd as CD
CT = CD.CT; T = CD.T; S = CD.S
from de4lib import Inst, wanted_goods, leftover


def lab(I, i, A, W):
    r = I.ranked(i)
    s = ''.join(sorted('abcd'[r.index(g)] for g in A)) or '0'
    if len(A) >= 2 and T.lev(I, i, A) == 6: s += '*'
    if len(A) == 1 and A[0] in W: s = 'F' + s
    return s

def role_sig(I, Y, Z, W, u, x, D):
    r = I.ranked(u)
    h = next(k for k in range(I.n) if r[0] in Y[k]); w = next((k for k in range(I.n) if r[1] in Y[k]), None)
    names = {u: 'u', x: 'x', h: 'h'}
    if w is not None and w not in names: names[w] = 'w'
    ch = [i for i in range(I.n) if set(Y[i]) != set(Z[i])]
    holder = {g: i for i in range(I.n) for g in Y[i]}
    parts = []
    for i in ch:
        nm = names.get(i, 'o')
        src = []
        for g in sorted(Z[i], key=lambda g: I.ranked(i).index(g)):
            hh = holder.get(g)
            src.append('abcd'[I.ranked(i).index(g)] + '<' + ('o' if hh == i else 'J' if hh is None else names.get(hh, 'o')))
        parts.append('%s:%s>%s[%s](%+d)' % (nm, lab(I, i, Y[i], W), lab(I, i, Z[i], W), ','.join(src), T.lev(I, i, Z[i]) - T.lev(I, i, Y[i])))
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
        lps = [(a[0], a[1], a[2]) for a in arcs if not CT.frozen(Y, a[0], W) and S.types(I, a[0], list(Y[a[0]])) == 'LP']
        if not lps: continue
        u, x, D = lps[0]
        C['(H) states with an out-arc of a lower-pair holder; top %s' % (p == P)] += 1
        if p == P: ex.append((tag, I.sets, [I.v[i] for i in range(I.n)], [list(A) for A in Y])); continue
        best = None; sigs = []
        for Z, q in zip(All, ph):
            if q <= p: continue
            k = sum(set(Y[i]) != set(Z[i]) for i in range(I.n))
            if best is None or k < best: best, sigs = k, [role_sig(I, Y, Z, W, u, x, D)]
            elif k == best: sigs.append(role_sig(I, Y, Z, W, u, x, D))
        C['  minimal raise size %s' % best] += 1
        lb = 'labelled' if set(D) & J else 'unlabelled'
        C['  arc %s, x %s' % (lb, lab(I, x, Y[x], W))] += 1
        for s_ in sorted(set(sigs))[:3]: C['    sig[%s] %s' % (best, s_)] += 1

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
        C['profiles'] += 1
        analyse(I, C, ex, src)
    return C, ex

if __name__ == '__main__':
    src, per, jobs, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    print('$ python3 k4/de4/lpout.py', ' '.join(sys.argv[1:]))
    tot, EX = collections.Counter(), []
    with mp.Pool(int(os.environ.get('NP', 2))) as p:
        for C, ex in p.imap_unordered(job, [(src, per, seed + k) for k in range(jobs)]): tot.update(C); EX += ex
    for k in sorted(tot): print('%7d  %s' % (tot[k], k))
    for e in EX[:6]: print('EX', json.dumps(e))
