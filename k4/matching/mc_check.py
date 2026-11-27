"""Lemma M^c (proof/k4-oc1max-multi, k4/oc1max_multi.md §9) checked with this note's own code, and the S^c shape as a
one-move criterion (k4/matching.md §5; evidence only).

(a) Lemma M^c's formula (mlib.M.mc_def, written here from the statement) against the raw S^c free-slot deficiency
    (mlib.M.deficiency with shape 'sc': pruned search, every candidate checked with raw EFX0), every owner, at states
    with (G2): the picks of every hard perfect start below and every 5th state one official move reaches;
(b) the pruned S^c search against the pruning-free brute force (mlib.M.bf_complete, shape 'sc', d = 0, 1) on a sample;
(c) "some official move gives an S^c completion" against OC1 (some move gives a one-absorber completion), at every
    hard perfect start below; S^c = one-absorber at single-good states (also checked).

Starts: the hard perfect starts of hard_{special,screen,suite,logs,cores_*,cex,pw_7_300}.jsonl, the 3,179 failing starts
of n4_failing_walk.jsonl (sampled for (a)), and the 60 starts of n4_nonsstar_walk.jsonl that OC1 repairs only
through a non-S* completion.

    python3 k4/matching/mc_check.py [STRIDE_FAIL]"""
import sys, os, json, glob, collections, time, multiprocessing as mp
import _mpaths  # noqa: F401
from mlib import M, INF


def g2(I, B):
    bv = [I.V(i, B[i]) for i in range(I.n)]
    return all(I.v[i].get(g, 0) <= bv[i] for g in I.junk(B) for i in range(I.n))


def job(args):
    row, src, full = args
    I = M(row['sets'], row['vals'], row.get('m')); Y = row['picks']; base = [[g] if g is not None else [] for g in Y]
    C = collections.Counter(); moves = I.moves(base)
    # (c) one-move criteria
    if src != 'fail':
        oc1 = any(I.complete(B, 0, 'oa') is not None for B in moves)
        sc1 = any(I.complete(B, 0, 'sc') is not None for B in moves)
        ss1 = any(I.complete(B, 0, 'ss') is not None for B in moves)
        C['%s: OC1 %s, some move gives S^c %s, some move gives S* %s' % (src, oc1, sc1, ss1)] += 1
    # single-good states: S^c = one absorber
    for o in range(I.n):
        a = I.complete(base, 0, 'sc', [o]) is not None; b = I.complete(base, 0, 'oa', [o]) is not None
        C['picks: S^c == one-absorber per owner %s' % (a == b)] += 1
    if not full: return C
    # (a) and (b)
    for k, B in enumerate([base] + moves[::5]):
        if not g2(I, B) or len(I.junk(B)) > 6: continue
        for o in range(I.n):
            md = I.mc_def(B, o); rd = I.deficiency(B, 'sc', [o])
            C['(a) M^c formula == raw S^c deficiency %s' % (md == rd)] += 1
            if md != rd: print('MC MISMATCH', json.dumps(row), B, o, md, rd, flush=True)
            if k % 3 == 0 and I.n <= 4:
                for d in (0, 1):
                    x = I.complete(B, d, 'sc', [o]) is not None; y = I.bf_complete(B, d, 'sc', o)
                    C['(b) pruned S^c search == brute force %s' % (x == y)] += 1
    return C


if __name__ == '__main__':
    STRIDE = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    R = os.path.join(_mpaths.ROOT, 'results', 'k4_matching'); tasks = []
    for f in ['hard_special', 'hard_screen', 'hard_suite', 'hard_logs', 'hard_cores_3000_91', 'hard_cores_1500_92', 'hard_cores_150_93',
              'hard_cex', 'hard_pw_7_300']:
        for l in open(os.path.join(R, f + '.jsonl')): tasks.append((json.loads(l), f, True))
    for l in open(os.path.join(R, 'n4_nonsstar_walk.jsonl')): tasks.append((json.loads(l), 'nonS*', True))
    for t, l in enumerate(open(os.path.join(R, 'n4_failing_walk.jsonl'))):
        tasks.append((json.loads(l), 'fail', t % STRIDE == 0))
    print('$ python3 k4/matching/mc_check.py', *sys.argv[1:], '|', len(tasks), 'starts', flush=True)
    T = collections.Counter(); t0 = time.time()
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for C in pool.imap_unordered(job, tasks, chunksize=4): T.update(C)
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
