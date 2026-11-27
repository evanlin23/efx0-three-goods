"""RKMAX and RKDOM from a failure export, with no OC1 computation (k4/rkmax.md §2–§3).

RKMAX (resp. RKDOM) says OC1 holds at every maximum matching whose signature sigma is lexicographically maximal
(resp. whose sorted rank vector no maximum matching dominates).  Contrapositive: every OC1-failing maximum-matching
start Y is sigma-dominated (resp. rank-dominated) by some maximum matching.  An export that lists EVERY failing
(type profile, picks) pair of a hypergraph therefore certifies both statements on that hypergraph's type profiles
(given the type reduction: sigma and dominance depend only on rankings of single goods, OC1 only on the type), once
every listed start is shown to be dominated.  This needs maximum matchings only.

Also recorded: the receivers' ranks at the failing start, and the fewest agents a dominating matching changes.
    python3 rk_dom_export.py FILE [STRIDE]"""
import sys, os, gzip, json, collections, time, multiprocessing as mp
from rklib import Prof
from rk_dominance import dom


def job(task):
    sets, starts = task
    C = collections.Counter(); ex = []
    for st in starts:
        P = Prof(sets, st['vals']); n = P.n
        nu, mm = P.max_matchings(); Y = tuple(st['picks'])
        C['starts'] += 1
        C['start is a maximum matching'] += sum(g is not None for g in Y) == nu
        rY = P.ranks(Y); sY = P.sigma(Y)
        better_sigma = [M for M in mm if P.sigma(M) > sY]
        domin = [M for M in mm if dom(P.ranks(M), rY)]
        C['sigma-dominated: %s' % bool(better_sigma)] += 1
        C['rank-dominated: %s' % bool(domin)] += 1
        ro = P.roles(Y)
        C['receiver ranks %s' % sorted(rY[u] for u in ro['U'])] += 1
        if domin:
            k = min(sum(1 for i in range(n) if M[i] != Y[i]) for M in domin)
            C['fewest agents changed by a dominating matching: %d' % k] += 1
            gain = set()
            for M in domin:
                if sum(1 for i in range(n) if M[i] != Y[i]) == k:
                    gain |= {i for i in range(n) if P.ranks(M)[i] < rY[i]}
            C['a minimal dominating change raises a receiver: %s' % bool(gain & set(ro['U']))] += 1
        if (not better_sigma or not domin) and len(ex) < 3:
            ex.append({'sets': sets, 'vals': st['vals'], 'picks': Y, 'sigma_dom': bool(better_sigma),
                       'rank_dom': bool(domin)})
    return C, ex


if __name__ == '__main__':
    F = sys.argv[1]; STRIDE = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    print('$ python3 k4/rkmax/rk_dom_export.py', os.path.basename(F), *sys.argv[2:], flush=True)
    d = json.load(gzip.open(F))
    tasks = []
    for h in d['hypergraphs']:
        print('hypergraph', h.get('list'), h['idx'], 'complete=%s' % h.get('complete', True), 'starts', len(h['starts']),
              flush=True)
        S = h['starts'][::STRIDE]
        for i in range(0, len(S), 64): tasks.append((h['sets'], S[i:i + 64]))
    T = collections.Counter(); t0 = time.time(); shown = 0
    with mp.Pool() as pool:
        for C, ex in pool.imap_unordered(job, tasks):
            T.update(C)
            for e in ex:
                if shown < 5: shown += 1; print('UNDOMINATED', json.dumps(e), flush=True)
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
