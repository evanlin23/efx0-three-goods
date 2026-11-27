"""RF-canon by FAIL-STRUCT₀ case (k4/sdc.md §31): for each failing start Y of d1's off-export walk dump and each receiver
u, YRMH-F's outcome Z (first listed order) is classified by OC1's raw check ('picks complete' / 'one move repairs'),
split by the number t of truly dangerous agents at Y (t = 0: case S2, the pick swap; t >= 2: case S1', competing
junk).  Also t at Z.  Guides a proof that splits on FAIL-STRUCT₀'s cases.
    python3 k4/sdc/rf_canon_bycase.py [STRIDE]"""
import os, sys, gzip, json, itertools, collections, multiprocessing as mp
import _paths  # noqa: F401
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'ttc'))
from oc1_mc2_rand import Inst
import rf_diag as D
import failstruct_check as FS

F = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'results', 'k4_rf_offexport',
                 'rf_walk_n5_stored_fails.jsonl.gz')


def tcount(I, Y):
    n = I.n; J = [g for g in range(I.m) if g not in Y]
    p = [I.v[i].get(Y[i], 0) if Y[i] is not None else 0 for i in range(n)]
    frozen = [j for j in range(n) if Y[j] is not None and any(i != j and I.v[i].get(Y[j], 0) > p[i] for i in range(n))]
    return sum(1 for j in frozen if sum(I.v[j].get(g, 0) for g in J) > p[j])


def job(r):
    I = Inst(r['sets'], r['vals']); Y = tuple(r['picks'])
    o = next(o for o in itertools.permutations(range(I.n)) if I.sd(o) == Y)
    t = tcount(I, Y); C = collections.Counter()
    for u in r['receivers']:
        Z, od = D.feasible_sd(I, Y, [u] + [a for a in o if a != u])
        res = 'stuck' if Z == ('stuck',) else I.check(Z)
        C['t(Y)=%d -> Z: %s' % (t, res)] += 1
        if Z != ('stuck',):
            tz = tcount(I, Z); C['t(Y)=%d -> t(Z)=%d' % (t, tz)] += 1
            FC, _ = FS.job((r['sets'], r['vals'], Z))
            s2 = any(k.startswith('shapes') and 'S2' in k for k in FC)
            s1p = FC.get("S1' (two D_T agents with intersecting minimal threatening junk sets): True", 0) > 0
            shaped = (tz == 0 and s2) or (tz >= 2 and s1p)
            C['Z has the FAIL-STRUCT0 shape: %s' % shaped] += 1
    return C


if __name__ == '__main__':
    S = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    print('$ python3 k4/sdc/rf_canon_bycase.py', *sys.argv[1:], flush=True)
    rows = [json.loads(l) for i, l in enumerate(gzip.open(F, 'rt')) if i % S == 0]
    print('starts', len(rows), flush=True)
    T = collections.Counter()
    with mp.Pool() as pool:
        for C in pool.imap_unordered(job, rows, chunksize=16): T.update(C)
    for k in sorted(T): print(k, T[k])
