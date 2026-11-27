"""The rank-dominating changes at OC1-failing starts (k4/rkmax.md §3): what are they?

At every exported failing start Y and every maximum matching M' that rank-dominates Y (sorted ranks, see
rk_dominance.py) and changes the fewest agents, describe the change Y -> M' as alternating components:
  - 'swap a<->b', 'cycle' (length >= 3), 'chain' (a_1 takes junk g, a_{s+1} takes Y_{a_s}, Y_{a_last} released);
  - for each agent of the change: its role at Y (U receiver, DT truly dangerous, D pick-dangerous, F frozen not
    dangerous), its old rank -> new rank, and whether it gains;
  - the rank intervals: a gainer's rise [r', r), a loser's drop [r, r').
Also tests the predicted shapes:
  (W1) a canonical one-step chain "k takes a junk good g in R_k, w takes Y_k" with k dangerous and w a wanter of Y_k,
       whose rise interval covers k's drop;
  (W2) the RF rotation (receiver first, RF-PATH) dominates.
    python3 rk_witness.py [FILE] [STRIDE]"""
import sys, os, gzip, json, itertools, collections, time, multiprocessing as mp
from rklib import Prof
from rk_dominance import dom

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')


def components(P, Y, M):
    """Decompose the change Y -> M (same agents, both matchings) into alternating components.
    Returns a list of (kind, [agents in order])."""
    n = P.n
    ch = [i for i in range(n) if Y[i] != M[i]]
    holderY = {Y[i]: i for i in range(n) if Y[i] is not None}
    seen = set(); out = []
    # chains: start at an agent whose new good was junk at Y (or that loses its good: pickless at M)
    for i in ch:
        if i in seen: continue
        if M[i] is not None and M[i] not in holderY:   # i takes a junk good: chain start
            seq = [i]; seen.add(i); cur = i
            while True:
                # who takes Y_cur?
                nxt = [j for j in ch if M[j] == Y[cur] and Y[cur] is not None]
                if not nxt: break
                cur = nxt[0]; seq.append(cur); seen.add(cur)
            out.append(('chain', seq))
    for i in ch:
        if i in seen: continue
        if M[i] is None:
            seq = [i]; seen.add(i); cur = i
            while True:
                nxt = [j for j in ch if M[j] == Y[cur] and Y[cur] is not None]
                if not nxt: break
                cur = nxt[0]; seq.append(cur); seen.add(cur)
            out.append(('drop', seq))
    for i in ch:
        if i in seen: continue
        seq = [i]; seen.add(i); cur = i
        while True:
            # cur takes Y_next
            nxt = holderY[M[cur]]
            if nxt == i: break
            seq.append(nxt); seen.add(nxt); cur = nxt
        out.append(('swap' if len(seq) == 2 else 'cycle%d' % len(seq), seq))
    return out


def role(ro, i):
    if i in ro['U']: return 'U'
    if i in ro['DT']: return 'DT'
    if i in ro['D']: return 'D'
    if i in ro['F']: return 'F'
    return '?'


def job(task):
    sets, vals, starts = task
    P = Prof(sets, vals); n = P.n
    nu, mm = P.max_matchings(); rk = {M: P.ranks(M) for M in mm}
    C = collections.Counter()
    for st in starts:
        Y = tuple(st['picks']); rY = rk[Y]; ro = P.roles(Y)
        D = [M for M in mm if dom(rk[M], rY)]
        if not D: C['undominated failing start'] += 1; continue
        k = min(sum(1 for i in range(n) if M[i] != Y[i]) for M in D)
        Dk = [M for M in D if sum(1 for i in range(n) if M[i] != Y[i]) == k]
        descs = set()
        for M in Dk:
            comps = components(P, Y, M)
            parts = []
            for kind, seq in comps:
                parts.append(kind + '[' + ' '.join('%s:%d>%d' % (role(ro, a), rY[a], rk[M][a]) for a in seq) + ']')
            descs.add(' + '.join(sorted(parts)))
        for dsc in descs: C['minimal dominating change: ' + dsc] += 1
        C['starts'] += 1
        # (W1): one-step chain k takes junk g, w takes Y_k, k dangerous, w wants Y_k, dominating
        w1 = False
        for (w, kk) in ro['wants']:
            if kk not in ro['D']: continue
            for g in ro['J']:
                if g not in P.rel[kk]: continue
                M = list(Y); M[kk] = g; M[w] = Y[kk]; M = tuple(M)
                if M in rk and dom(rk[M], rY): w1 = True
        C['(W1) one-step chain from a dangerous agent dominates: %s' % w1] += 1
        # (W2): RF rotation from each receiver over the listed orders
        for u in st.get('receivers', ro['U']):
            any_d = False
            for o in st['orders']:
                o2 = (u,) + tuple(i for i in o if i != u)
                M = P.sd(o2)
                if M in rk and dom(rk[M], rY): any_d = True
            C['(W2) RF rotation (some listed order) dominates: %s' % any_d] += 1
    return C


if __name__ == '__main__':
    F = sys.argv[1] if len(sys.argv) > 1 and not sys.argv[1].isdigit() else os.path.join(
        ROOT, 'results', 'k4_oc1max', 'two_move_starts_n4.json.gz')
    STRIDE = int(sys.argv[-1]) if len(sys.argv) > 1 and sys.argv[-1].isdigit() else 1
    print('$ python3 k4/rkmax/rk_witness.py', *sys.argv[1:], flush=True)
    d = json.load(gzip.open(F))
    prof = collections.OrderedDict()
    for h in d['hypergraphs']:
        for st in h['starts']:
            key = (json.dumps(h['sets']), json.dumps(st['vals']))
            prof.setdefault(key, (h['sets'], st['vals'], []))[2].append(st)
    tasks = list(prof.values())[::STRIDE]
    print('profiles', len(tasks), 'starts', sum(len(t[2]) for t in tasks), flush=True)
    T = collections.Counter(); t0 = time.time()
    with mp.Pool() as pool:
        for C in pool.imap_unordered(job, tasks, chunksize=8): T.update(C)
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
