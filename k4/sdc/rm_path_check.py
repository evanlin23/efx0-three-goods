"""RF versus the rank signature (k4/sdc.md §31, Conjecture RKMAX): at every OC1^max-failing start Y of an export and
every receiver u, and every listed order o of Y, let Y' = SD(u, o - u) (RF-PATH's rotation).  Classify:
  - ejected agents E = {i != u : Y'_i != Y_i}; does some i in E hold its top good at Y ("ejected top-holder")?
  - is Y' a maximum matching, and is sigma(Y') > sigma(Y) (rank-maximal order: (#rank1, ..., #rank4) lexicographic)?
Expected (by the level-1 count): no ejected top-holder ==> sigma(Y') > sigma(Y), since u moves to rank 1.
    python3 k4/sdc/rm_path_check.py FILE [STRIDE]"""
import sys, os, gzip, json, collections, time, multiprocessing as mp
import _paths  # noqa: F401
from oc1_mc2_rand import Inst
from oc1_max_orders import nu
from extremal_rank_check import ranks, POT

RM = POT['RM']


def job(a):
    sets, st = a
    I = Inst(sets, st['vals']); n = I.n; N = nu(I); Y = tuple(st['picks']); rY = ranks(I, Y)
    rec = [u for u in range(n) if Y[u] is not None and all(I.v[i].get(Y[u], 0) <= I.v[i].get(Y[i], 0) for i in range(n) if i != u)]
    C = collections.Counter(); C['starts'] += 1
    for u in rec:
        anyb = False; anyclean = False
        for o in st['orders']:
            o = tuple(o); Y2 = I.sd((u,) + tuple(i for i in o if i != u))
            mm = sum(x is not None for x in Y2) == N
            E = [i for i in range(n) if i != u and Y2[i] != Y[i]]
            top = any(rY[i] == 1 for i in E)
            better = mm and RM(ranks(I, Y2)) > RM(rY)
            C['(Y,u,o): max=%s ejected-top-holder=%s RM-better=%s' % (mm, top, better)] += 1
            anyb |= better; anyclean |= (mm and not top)
        C['(Y,u): some listed order RM-better: %s' % anyb] += 1
        C['(Y,u): some listed order max with no ejected top-holder: %s' % anyclean] += 1
    return C


if __name__ == '__main__':
    F = sys.argv[1]; STRIDE = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    print('$ python3 k4/sdc/rm_path_check.py', *sys.argv[1:], flush=True)
    d = json.load(gzip.open(F))
    tasks = [(h['sets'], st) for h in d['hypergraphs'] for st in h['starts']][::STRIDE]
    print('starts', len(tasks), flush=True)
    T = collections.Counter(); t0 = time.time()
    with mp.Pool() as pool:
        for C in pool.imap_unordered(job, tasks, chunksize=64): T.update(C)
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
