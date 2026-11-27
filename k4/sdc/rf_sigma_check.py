"""RFσ, a canonical RF-exists rule (k4/sdc.md §31): at an OC1-failing maximum-matching start Y and each receiver u
(holding a pick), take the u-first maximum-matching SD vectors whose rank signature sigma (#rank 1, #rank 2, ...) is
lexicographically maximal among the u-first maximum-matching vectors; does OC1 hold at all of them ('every') / at one
('some')?  Ranks run to the instance's k.  Inputs: an export file (every failing (profile, picks) pair) or the built-in
k = 5 twin instance.
    python3 k4/sdc/rf_sigma_check.py FILE [STRIDE]   |   python3 k4/sdc/rf_sigma_check.py twin"""
import sys, gzip, json, itertools, collections, multiprocessing as mp
import _paths  # noqa: F401
from oc1_mc2_rand import Inst
from oc1_max_orders import nu


def sig(I, p, K):
    r = [1 + sum(1 for g in I.R[i] if I.v[i][g] > I.v[i][p[i]]) for i in range(I.n) if p[i] is not None]
    return tuple(sum(1 for x in r if x == t) for t in range(1, K + 1))


def job(a):
    sets, vals, Y = a
    I = Inst(sets, vals); n = I.n; N = nu(I); K = max(len(s) for s in sets); Y = tuple(Y)
    rec = [u for u in range(n) if Y[u] is not None and all(I.v[i].get(Y[u], 0) <= I.v[i].get(Y[i], 0) for i in range(n) if i != u)]
    C = collections.Counter(); ex = None
    for u in rec:
        vs = set(I.sd((u,) + rest) for rest in itertools.permutations([i for i in range(n) if i != u]))
        mm = [p for p in vs if sum(x is not None for x in p) == N]
        if not mm: C['(Y,u) with no u-first max vector'] += 1; continue
        best = max(sig(I, p, K) for p in mm); O = [p for p in mm if sig(I, p, K) == best]
        res = {p: I.check(p) for p in O}
        ev = all(r != 'OC1 fails' for r in res.values()); so = any(r != 'OC1 fails' for r in res.values())
        C['(Y,u) pairs'] += 1; C['RFsigma every: %s' % ev] += 1; C['RFsigma some: %s' % so] += 1
        if not ev and ex is None: ex = (sets, vals, Y, u, [(p, sig(I, p, K), res[p]) for p in O])
    return C, ex


if __name__ == '__main__':
    print('$ python3 k4/sdc/rf_sigma_check.py', *sys.argv[1:], flush=True)
    if sys.argv[1] == 'twin':
        tasks = [([[0, 1, 2, 5, 6], [1, 2, 4, 5, 6], [3, 4, 5, 6], [3, 4, 5, 6]],
                  [[3, 35, 33, 43, 39], [20, 26, 16, 43, 32], [8, 2, 7, 4], [8, 2, 7, 4]], (6, 5, 4, 3))]
    else:
        d = json.load(gzip.open(sys.argv[1])); S = int(sys.argv[2]) if len(sys.argv) > 2 else 1
        tasks = [(h['sets'], st['vals'], st['picks']) for h in d['hypergraphs'] for st in h['starts']][::S]
    print('starts', len(tasks), flush=True)
    T = collections.Counter(); shown = 0
    with mp.Pool() as pool:
        for C, ex in pool.imap_unordered(job, tasks, chunksize=32):
            T.update(C)
            if ex and shown < 3: shown += 1; print('RFsigma-every FAILS', json.dumps(ex), flush=True)
    for k in sorted(T): print(k, T[k])
