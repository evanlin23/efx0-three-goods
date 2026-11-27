"""RF-canon via REC-LOW (k4/sdc.md §31): REC-LOW says an OC1-failing maximum-matching start has every receiver at rank
>= 3.  YRMH-F with receiver u first usually hands u its top good.  For each failing start Y of d1's off-export walk dump
and each receiver u, at Z = YRMH-F(Y, u first): u's rank at Z, whether u is still a receiver at Z, the smallest rank of a
receiver at Z, and whether Z escapes REC-LOW's failure shape (no receiver, or a receiver at rank <= 2), split by Z's
OC1 outcome; where Z is in REC-LOW's shape, whether it is also in FAIL-STRUCT0's (rf_canon_bycase.py).
    python3 k4/sdc/rf_canon_recrank.py [STRIDE]"""
import os, sys, gzip, json, itertools, collections, multiprocessing as mp
import _paths  # noqa: F401
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'ttc'))
from oc1_mc2_rand import Inst
from extremal_rank_check import ranks
import rf_diag as D
import failstruct_check as FS
from rf_canon_bycase import tcount

F = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'results', 'k4_rf_offexport',
                 'rf_walk_n5_stored_fails.jsonl.gz')


def recs(I, Y):
    n = I.n; p = [I.v[i].get(Y[i], 0) if Y[i] is not None else 0 for i in range(n)]
    return [u for u in range(n) if Y[u] is not None and all(I.v[i].get(Y[u], 0) <= p[i] for i in range(n) if i != u)]


def job(r):
    I = Inst(r['sets'], r['vals']); Y = tuple(r['picks'])
    o = next(o for o in itertools.permutations(range(I.n)) if I.sd(o) == Y)
    C = collections.Counter()
    for u in r['receivers']:
        Z, od = D.feasible_sd(I, Y, [u] + [a for a in o if a != u])
        if Z == ('stuck',): C['stuck'] += 1; continue
        rk = ranks(I, Z); rz = recs(I, Z); res = I.check(Z)
        esc = (not rz) or min(rk[a] for a in rz) <= 2
        C['pairs'] += 1
        C['u rank at Z %d' % rk[u]] += 1
        C['u receiver at Z: %s' % (u in rz)] += 1
        C['min receiver rank at Z: %s' % (min(rk[a] for a in rz) if rz else 'no receiver')] += 1
        C['Z escapes the REC-LOW shape: %s -> %s' % (esc, res)] += 1
        if not esc:
            tz = tcount(I, Z); FC, _ = FS.job((r['sets'], r['vals'], Z))
            s2 = any(k.startswith('shapes') and 'S2' in k for k in FC)
            s1p = FC.get("S1' (two D_T agents with intersecting minimal threatening junk sets): True", 0) > 0
            shaped = (tz == 0 and s2) or (tz >= 2 and s1p)
            C['  in the REC-LOW shape: also in the FAIL-STRUCT0 shape: %s -> %s' % (shaped, res)] += 1
    return C


if __name__ == '__main__':
    S = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    print('$ python3 k4/sdc/rf_canon_recrank.py', *sys.argv[1:], flush=True)
    rows = [json.loads(l) for i, l in enumerate(gzip.open(F, 'rt')) if i % S == 0]
    print('starts', len(rows), flush=True)
    T = collections.Counter()
    with mp.Pool() as pool:
        for C in pool.imap_unordered(job, rows, chunksize=16): T.update(C)
    for k in sorted(T): print(k, T[k])
