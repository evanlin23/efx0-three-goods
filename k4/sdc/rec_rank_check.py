"""Receiver rank at OC1-failing maximum-matching starts (k4/sdc.md §31): at every failing start Y, which rank does each
receiver u hold (rank_u(Y) = 1 + #goods u values more than Y_u; receivers: pick holders whose pick no other agent
values above its own pick)?  Candidate REC-LOW: every receiver holds its rank-3 or rank-4 good (never its top two).
Sources: the complete n = 4 export, the n = 5 exports (sel2 complete for 5_pure #419, #447, #38; partial6), d1's
off-export walk dump (jsonl), and the named k = 4 / k = 5 failures of failstruct_extra.py.
    python3 k4/sdc/rec_rank_check.py FILE [STRIDE]   |   python3 k4/sdc/rec_rank_check.py extra"""
import sys, os, gzip, json, collections, multiprocessing as mp
import _paths  # noqa: F401
from oc1_mc2_rand import Inst
from extremal_rank_check import ranks


def job(a):
    sets, vals, Y = a; I = Inst(sets, vals); Y = tuple(Y); n = I.n; rk = ranks(I, Y)
    p = [I.v[i].get(Y[i], 0) if Y[i] is not None else 0 for i in range(n)]
    rec = [u for u in range(n) if Y[u] is not None and all(I.v[i].get(Y[u], 0) <= p[i] for i in range(n) if i != u)]
    C = collections.Counter(); C['starts'] += 1; C['starts with %d receivers' % len(rec)] += 1
    for u in rec: C['receiver holds rank %d of %d' % (rk[u], len(sets[u]))] += 1
    low = all(rk[u] >= 3 for u in rec)
    C['REC-LOW (every receiver holds rank >= 3): %s' % low] += 1
    return C, (None if low else (sets, vals, list(Y), [(u, rk[u]) for u in rec]))


if __name__ == '__main__':
    print('$ python3 k4/sdc/rec_rank_check.py', *sys.argv[1:], flush=True)
    if sys.argv[1] == 'extra':
        import failstruct_extra as FE
        for name, (s, v, y) in FE.CASES.items():
            C, ex = job((s, v, y)); print(name, sorted(k for k in C if k.startswith('rec') or k.startswith('REC')))
        sys.exit()
    S = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    if sys.argv[1].endswith('.jsonl.gz'):
        tasks = [(r['sets'], r['vals'], r['picks']) for r in map(json.loads, gzip.open(sys.argv[1], 'rt'))][::S]
    else:
        d = json.load(gzip.open(sys.argv[1]))
        tasks = [(h['sets'], st['vals'], st['picks']) for h in d['hypergraphs'] for st in h['starts']][::S]
    T = collections.Counter(); shown = 0
    with mp.Pool() as pool:
        for C, ex in pool.imap_unordered(job, tasks, chunksize=256):
            T.update(C)
            if ex and shown < 3: shown += 1; print('REC-LOW FAILS', json.dumps(ex), flush=True)
    for k in sorted(T): print(k, T[k])
