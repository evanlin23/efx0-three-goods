"""Is every OC1-failing maximum-matching start rank-dominated? (k4/rkmax.md §3)

For matchings M, M' write M' >_D M (anonymous rank dominance) if the sorted rank vectors satisfy
sort(rank(M'))[k] <= sort(rank(M))[k] for every k, with some strict inequality.  Every rank potential that is monotone
for this order (RM = lexicographic signature, RS = rank sum, LMR = leximin) is then strictly larger at M'.
Also the per-agent form M' >_P M (rank_i(M') <= rank_i(M) for every i, some strict), which is Pareto dominance and
cannot hold at SD outcomes, as a sanity check.

At every exported failing start Y (results/k4_oc1max/two_move_starts_n4.json.gz, or an n = 5 export given as FILE):
  - is some maximum matching M' >_D Y?  Is some M' >_D Y an SD outcome that satisfies OC1?  (OC1 checked only when
    asked, CHECK=1.)
  - the minimal witnesses: the rotation RF-PATH gives, and how many agents change.
    python3 rk_dominance.py [FILE] [STRIDE]"""
import sys, os, gzip, json, itertools, collections, time, multiprocessing as mp
from rklib import Prof

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')
CHECK = os.environ.get('CHECK', '0') == '1'


def dom(a, b):
    """sorted a dominates sorted b (a better: smaller ranks)"""
    sa, sb = sorted(a), sorted(b)
    return all(x <= y for x, y in zip(sa, sb)) and sa != sb


def job(task):
    sets, vals, starts = task
    P = Prof(sets, vals); n = P.n
    nu, mm = P.max_matchings()
    rk = {M: P.ranks(M) for M in mm}
    C = collections.Counter()
    for st in starts:
        Y = tuple(st['picks']); rY = rk[Y]
        C['starts'] += 1
        D = [M for M in mm if dom(rk[M], rY)]
        C['some max matching rank-dominates Y: %s' % bool(D)] += 1
        Pd = [M for M in mm if all(a <= b for a, b in zip(rk[M], rY)) and rk[M] != rY]
        C['some max matching Pareto-dominates Y in ranks (expect False): %s' % bool(Pd)] += 1
        if D:
            k = min(sum(1 for i in range(n) if M[i] != Y[i]) for M in D)
            C['  fewest agents changed by a dominating matching: %d' % k] += 1
            undom = [M for M in D if not any(dom(rk[M2], rk[M]) for M2 in mm)]
            C['  some dominating matching is itself undominated: %s' % bool(undom)] += 1
            if CHECK:
                ok = any(P.oc1(M) != 'F' for M in undom)
                C['  some undominated dominating matching satisfies OC1: %s' % ok] += 1
        else:
            print('UNDOMINATED FAILING START', json.dumps({'sets': sets, 'vals': vals, 'picks': Y, 'ranks': rY}),
                  flush=True)
    # undominated maximum matchings of the profile: does OC1 hold at all of them?
    if CHECK:
        und = [M for M in mm if not any(dom(rk[M2], rk[M]) for M2 in mm)]
        r = [P.oc1(M) for M in und]
        C['profiles'] += 1
        C['undominated max matchings'] += len(und)
        for x in r: C['undominated max matching OC1 ' + x] += 1
        C['profiles where every undominated max matching satisfies OC1'] += all(x != 'F' for x in r)
    return C


if __name__ == '__main__':
    F = sys.argv[1] if len(sys.argv) > 1 and not sys.argv[1].isdigit() else os.path.join(
        ROOT, 'results', 'k4_oc1max', 'two_move_starts_n4.json.gz')
    STRIDE = int(sys.argv[-1]) if len(sys.argv) > 1 and sys.argv[-1].isdigit() else 1
    print('$ CHECK=%d python3 k4/rkmax/rk_dominance.py' % CHECK, *sys.argv[1:], flush=True)
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
