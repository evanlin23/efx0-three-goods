"""LIFT-SHAPE+ and CM2 on the proof/k4-oc1max-multi session's 4,955 failing (profile, start) pairs (k4/matching.md §6).

Data: results/k4_matching/data/multi_oc1_fail_walk.jsonl.gz, a copy of results/k4_oc1max_multi/oc1_fail_walk.jsonl.gz on
branch proof/k4-oc1max-multi (value walks near the 12 known failures; 4,378 with n = 4 and 577 with n = 5 near the
TTC session's core).  For every row, independently of that session's code:
  1. the picks are the serial-dictatorship picks of the stored order, every agent picks, there is no one-absorber
     completion at the picks and none after any official move (raw; mlib.complete, Inst.moves);
  2. LIFT-SHAPE+ with (L1)-(L3), and Lemma LIFT-1's construction checked with raw EFX0 (lift1_check.job);
  3. CM2: some first move followed by a Lemma EX* exchange (cm2.job), and whether EX* is exact on the second move.

    python3 k4/matching/multi_check.py [STRIDE]"""
import sys, os, gzip, json, collections, time, multiprocessing as mp
import _mpaths  # noqa: F401
from mlib import M
import lift1_check, cm2


def job(row):
    I = M(row['sets'], row['vals']); Y = tuple(row['picks']); C = collections.Counter(); n = I.n
    C['n = %d' % n] += 1
    base = [[g] for g in Y]
    ok = I.sd(row['order']) == Y and all(y is not None for y in Y) and I.complete(base, 0, 'oa') is None and \
        not any(I.complete(B1, 0, 'oa') is not None for B1 in I.moves(base))
    C['n = %d: verified (perfect SD start, no one-move repair, raw) %s' % (n, ok)] += 1
    if not ok: return C
    for k, v in lift1_check.job(dict(sets=row['sets'], vals=row['vals'], picks=list(Y))).items(): C['n = %d: %s' % (n, k)] += v
    _, _, nf, ne, no, C2 = cm2.job((row.get('name', ''), row['sets'], row['vals'], Y))
    C['n = %d: CM2 %s' % (n, ne > 0)] += 1
    C['n = %d: EX* exact on the second move (first moves with an EX* exchange = first moves after which some move repairs) %s' % (n, ne == no)] += 1
    return C


if __name__ == '__main__':
    STRIDE = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    p = os.path.join(_mpaths.ROOT, 'results', 'k4_matching', 'data', 'multi_oc1_fail_walk.jsonl.gz')
    rows = [json.loads(l) for l in gzip.open(p, 'rt')][::STRIDE]
    print('$ python3 k4/matching/multi_check.py', *sys.argv[1:], '|', len(rows), 'rows', flush=True)
    T = collections.Counter(); t0 = time.time(); done = 0
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for C in pool.imap_unordered(job, rows, chunksize=4):
            T.update(C); done += 1
            if done % 500 == 0: print('...', done, '%.0f s' % (time.time() - t0), flush=True)
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
