"""TTC's canonical RF-exists rule YRMH-F (k4/ttc.md §14.9; k4/ttc/rf_diag.feasible_sd) on d1's off-export walk dump
(results/k4_rf_offexport/rf_walk_n5_stored_fails.jsonl.gz: OC1-failing maximum-matching n = 5 starts with their SD
orders and receivers).  For each (start, receiver u) and each listed order o (up to MAXO): queue (u, o - u), YRMH-F's
outcome; it works if it is a maximum matching with u first and OC1 holds (oc1_mc2_rand.Inst.check).  Reports per
(start, receiver): works for the first listed order / for some listed order; and per start: some receiver works.
    python3 k4/sdc/rf_canon_offexport.py [STRIDE] [MAXO]"""
import os, sys, gzip, json, itertools, collections, multiprocessing as mp
import _paths  # noqa: F401
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'ttc'))
from oc1_mc2_rand import Inst
import rf_diag as D

F = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'results', 'k4_rf_offexport',
                 'rf_walk_n5_stored_fails.jsonl.gz')
MAXO = 3


def job(r):
    I = Inst(r['sets'], r['vals']); Y = tuple(r['picks']); size = sum(y is not None for y in Y)
    C = collections.Counter(); cache = {}; some_rec = False; ex = None
    ords = [o for o in itertools.permutations(range(I.n)) if I.sd(o) == Y][:MAXO]  # the dump stores only their count
    for u in r['receivers']:
        oks = []
        for o in ords:
            q = [u] + [a for a in o if a != u]
            Z, od = D.feasible_sd(I, Y, q)
            if Z == ('stuck',):
                oks.append(False); C['YRMH-F stuck'] += 1; continue
            if Z not in cache:
                cache[Z] = sum(z is not None for z in Z) >= size and I.check(Z) != 'OC1 fails'
            oks.append(cache[Z] and od[0] == u)
        C['(start, receiver) pairs'] += 1
        C['YRMH-F works, first listed order: %s' % oks[0]] += 1
        C['YRMH-F works, some listed order: %s' % any(oks)] += 1
        some_rec |= any(oks)
        if not oks[0] and ex is None: ex = (r['sets'], r['vals'], Y, u, ords)
    C['starts'] += 1; C['some receiver and listed order works: %s' % some_rec] += 1
    return C, ex


if __name__ == '__main__':
    S = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    if len(sys.argv) > 2: MAXO = int(sys.argv[2])
    print('$ python3 k4/sdc/rf_canon_offexport.py', *sys.argv[1:], flush=True)
    rows = [json.loads(l) for i, l in enumerate(gzip.open(F, 'rt')) if i % S == 0]
    print('starts', len(rows), flush=True)
    T = collections.Counter(); shown = 0
    with mp.Pool() as pool:
        for C, ex in pool.imap_unordered(job, rows, chunksize=16):
            T.update(C)
            if ex and shown < 3: shown += 1; print('FIRST-ORDER MISS', json.dumps(ex), flush=True)
    for k in sorted(T): print(k, T[k])
