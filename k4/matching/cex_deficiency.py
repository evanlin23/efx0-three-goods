"""Free-slot deficiency on the known OC1 counterexamples (k4/matching.md §2).

  PW5 (k = 5, k4/ksens.md §1), its k = 4 version PW4 (pool of three goods), RD5 (k = 5, k4/ksens.md §6) and its k = 4
  version RD4 (agent 0 without good 4), B< and B> (k4/sdc.md §31, n = 6), and the 39 core counterexamples of
  results/k4_sdc/ttc_core_cex_39.json.
For every distinct pick vector of every order: maximum matching or not, delta_oa at the picks, whether OC1 holds
(some official move reaches delta_oa = 0), and the least delta_oa one move reaches.

    python3 k4/matching/cex_deficiency.py [names...]"""
import sys, os, json, itertools, collections, time, multiprocessing as mp
import _mpaths  # noqa: F401
from mlib import M, INF

PW5 = ([[0, 5, 6, 7, 8], [1, 5, 6, 7, 8], [2, 5, 6, 7, 8], [0, 1, 2, 3], [0, 1, 2, 4]],
       [[10, 9, 8, 7, 6]] * 3 + [[6, 4, 2, 1], [6, 4, 2, 1]])
PW4 = ([[0, 5, 6, 7], [1, 5, 6, 7], [2, 5, 6, 7], [0, 1, 2, 3], [0, 1, 2, 4]],
       [[10, 9, 8, 7]] * 3 + [[6, 4, 2, 1], [6, 4, 2, 1]])
RD5 = ([[0, 3, 4, 5, 1], [1, 2, 3], [1, 3, 4, 2], [0, 2, 6, 5]],
       [[26, 44, 24, 33, 57], [12, 11, 6], [9, 6, 1, 8], [36, 53, 4, 47]])
RD4 = ([[0, 3, 5, 1], [1, 2, 3], [1, 3, 4, 2], [0, 2, 6, 5]],
       [[26, 44, 33, 57], [12, 11, 6], [9, 6, 1, 8], [36, 53, 4, 47]])
BLT = ([[0, 2, 3, 1], [6, 4, 5, 9], [1, 2, 3, 9], [1, 6, 7, 8], [3, 6, 9], [1, 3, 6, 9]],
       [[6, 14, 16, 12], [4, 18, 12, 28], [28, 4, 16, 21], [16, 14, 12, 6], [28, 8, 24], [20, 30, 8, 4]])
BGT = (BLT[0], [BLT[1][0], BLT[1][1], [28, 4, 16, 19], BLT[1][3], BLT[1][4], BLT[1][5]])


def instances():
    out = [('PW5', *PW5), ('PW4', *PW4), ('RD5', *RD5), ('RD4', *RD4), ('B<', *BLT), ('B>', *BGT)]
    for t, d in enumerate(json.load(open(os.path.join(_mpaths.ROOT, 'results', 'k4_sdc', 'ttc_core_cex_39.json')))):
        out.append(('cex39-%d' % t, d['sets'], d['vals']))
    return out


def job(item):
    name, sets, vals = item
    I = M(sets, vals, None, name); NU = I.nu(); C = collections.Counter(); rows = []
    for Y in sorted(set(I.sd(o) for o in itertools.permutations(range(I.n))), key=str):
        base = [[g] if g is not None else [] for g in Y]
        kind = 'max' if sum(1 for y in Y if y is not None) == NU else 'non-max'
        d = I.deficiency(base, 'oa')
        if d == 0:
            C[(kind, 'delta 0 (complete at the picks)')] += 1; continue
        after = [I.deficiency(b, 'oa', dmax=d) for b in I.moves(base)]
        best = min(after) if after else INF
        C[(kind, 'delta %d, best after one move %s, OC1 %s' % (d, best, 'holds' if best == 0 else 'FAILS'))] += 1
        rows.append((Y, kind, d, best))
    return name, len(sets), max(map(len, sets)), C, rows


if __name__ == '__main__':
    want = set(sys.argv[1:])
    items = [it for it in instances() if not want or it[0] in want]
    print('$ python3 k4/matching/cex_deficiency.py', *sys.argv[1:], flush=True)
    T = collections.Counter(); t0 = time.time()
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for name, n, k, C, rows in pool.imap(job, items):
            print('%s (n = %d, k = %d):' % (name, n, k), '; '.join('%s %s: %d' % (a, b, c) for (a, b), c in sorted(C.items())),
                  flush=True)
            for (a, b), c in C.items(): T[('k=%d' % k, a, b)] += c
            for Y, kind, d, best in rows:
                if best > 0: print('    OC1 fails at picks', list(Y), kind, 'delta', d, 'best after one move', best)
    print('totals (distinct pick vectors):')
    for key in sorted(T): print('  ', *key, T[key])
    print('time %.0f s' % (time.time() - t0))
