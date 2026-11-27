"""Starved receivers at OC1-failing starts (k4/rkmax.md §4).

At every exported failing start Y: the receivers' ranks; for the receiver u of largest rank, the holder x of u's top
good t; x's rank, and x's *fallbacks*: goods of R_x that are free once u takes t, i.e. Y_u and the junk goods x values,
with their ranks for x.  Tests the dominance step of Lemma STARVE (k4/rkmax.md §4):
  (S1) some receiver u has rank >= 3;
  (S2) for some receiver u and some good g that u prefers to Y_u, held by x, x has a fallback f with
       [r_x, rank_x(f)) inside [rank_u(g), r_u) and not equal (the 2-agent change dominates, Lemma 2AG);
  (S3) the same with g = u's top;
  roles of x (dangerous? truly dangerous? in Theta(u)?) when (S3) holds.
    python3 rk_starve.py FILE [STRIDE]"""
import sys, os, gzip, json, collections, time, multiprocessing as mp
from rklib import Prof


def theta(P, Y, ro, z):
    """Theta(z): dangerous agents threatened by J + Y_z at their pick value (k4/oc1max_multi.md §2)."""
    W = list(ro['J']) + [Y[z]]
    return [d for d in ro['D'] if P.threat(d, P.val[d][Y[d]], W)]


def job(task):
    sets, starts = task
    C = collections.Counter()
    for st in starts:
        P = Prof(sets, st['vals']); n = P.n; Y = tuple(st['picks'])
        r = P.ranks(Y); ro = P.roles(Y); J = set(ro['J'])
        holder = {Y[i]: i for i in range(n) if Y[i] is not None}
        C['starts'] += 1
        C['receiver ranks %s' % sorted(r[u] for u in ro['U'])] += 1
        C['(S1) some receiver has rank >= 3: %s' % any(r[u] >= 3 for u in ro['U'])] += 1
        s2 = s3 = False; s3info = set()
        for u in ro['U']:
            for g in P.rel[u]:
                if P.val[u][g] <= P.val[u][Y[u]]: continue
                x = holder[g]; ru2 = P.rank(u, g)
                fb = [f for f in P.rel[x] if f == Y[u] or f in J]
                for f in fb:
                    rx2 = P.rank(x, f)
                    if ru2 <= r[x] and rx2 <= r[u] and not (ru2 == r[x] and rx2 == r[u]):
                        s2 = True
                        if ru2 == 1:
                            s3 = True
                            th = theta(P, Y, ro, u)
                            s3info.add('x role %s, x in Theta(u) %s, fallback %s, ranks u %d>1 x %d>%d' % (
                                'DT' if x in ro['DT'] else 'D' if x in ro['D'] else 'F', x in th,
                                'Y_u' if f == Y[u] else 'junk', r[u], r[x], rx2))
        C['(S2) a dominating 2-agent change through a receiver: %s' % s2] += 1
        C['(S3) ... with the receiver taking its top: %s' % s3] += 1
        for s in s3info: C['   (S3) ' + s] += 1
    return C


if __name__ == '__main__':
    F = sys.argv[1]; STRIDE = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    print('$ python3 k4/rkmax/rk_starve.py', os.path.basename(F), *sys.argv[2:], flush=True)
    d = json.load(gzip.open(F))
    tasks = []
    for h in d['hypergraphs']:
        S = h['starts'][::STRIDE]
        for i in range(0, len(S), 64): tasks.append((h['sets'], S[i:i + 64]))
    T = collections.Counter(); t0 = time.time()
    with mp.Pool() as pool:
        for C in pool.imap_unordered(job, tasks): T.update(C)
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
