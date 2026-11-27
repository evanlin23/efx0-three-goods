"""REC-LOW's escape side on the complete n = 4 failure export (k4/sdc.md §31, K4.SDC.RECLOW): over every STRIDE-th
profile of results/k4_oc1max/two_move_starts_n4.json.gz (all 24 orders), at each maximum-matching SD vector with no
receiver or with a receiver at rank <= 2, how OC1 holds (raw checker; absorbers as in rf_canon_absorber.py), by the
smallest receiver rank; at rank 1, whether a top-holding receiver can be the absorber.
    python3 k4/sdc/rec_low_outcome.py [STRIDE]"""
import sys, os, gzip, json, itertools, collections, multiprocessing as mp
import _paths  # noqa: F401
from oc1_mc2_rand import Inst
from oc1_max_orders import nu
from extremal_rank_check import ranks
from rec_low_rand import recs
from rf_canon_absorber import absorbers
def job(a):
    sets, vals = a; I = Inst(sets, vals); n = I.n; N = nu(I); C = collections.Counter()
    for Y in set(I.sd(o) for o in itertools.permutations(range(n))):
        if sum(x is not None for x in Y) != N: continue
        rz = recs(I, Y); rk = ranks(I, Y)
        if not rz: C['no receiver'] += 1; continue
        mr = min(rk[u] for u in rz)
        if mr > 2: continue
        base = [[p] if p is not None else [] for p in Y]
        A, _ = absorbers(I, base)
        res = 'picks complete' if A else I.check(Y)
        C['min receiver rank %d -> %s' % (mr, res)] += 1
        if mr == 1 and A:
            tops = [u for u in rz if rk[u] == 1]
            C['rank1: some top-holding receiver absorbs: %s' % any(u in A for u in tops)] += 1
            C['rank1: some top-holding receiver absorbs, or None: %s' % (None in A or any(u in A for u in tops))] += 1
    return C
if __name__ == '__main__':
    print('$ python3 k4/sdc/rec_low_outcome.py', *sys.argv[1:], flush=True)
    d = json.load(gzip.open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'results', 'k4_oc1max',
                                         'two_move_starts_n4.json.gz')))
    prof = {}
    for h in d['hypergraphs']:
        for st in h['starts']: prof[(json.dumps(h['sets']), json.dumps(st['vals']))] = (h['sets'], st['vals'])
    tasks = list(prof.values())[::int(sys.argv[1]) if len(sys.argv) > 1 else 1]
    T = collections.Counter()
    with mp.Pool() as pool:
        for C in pool.imap_unordered(job, tasks, chunksize=16): T.update(C)
    print('profiles', len(tasks))
    for k in sorted(T): print(k, T[k])
