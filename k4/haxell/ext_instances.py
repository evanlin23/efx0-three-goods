"""Instances from other workstreams, copied verbatim with their sources (read at origin on 2026-11-26), for the CONN_2
tests of k4/haxell.md §5.  Nothing here is re-derived; see the source files for how each was found and checked.

  PW5, PW4      k4/ksens/refute_oc_k5.py (branch claude/k4-ksens): OC/OC1 counterexample at k = 5 (refereed), and
                its k = 4 version (pool of three goods)
  RD5, RD4      k4/ksens/refute_rd_k5.py: one round of disjoint chains fails at k = 5; RD4 = agent 0 without good 4
                (k4/ksens.md §6, "the k = 4 version")
  KG8, KG7      attempts/kgen-n4-oc1.md (branch claude/kgen-n3): OC1 fails at n = 4, k = 5 (strict, m = 8; ties, m = 7)
  TTC0..TTC38   results/k4_sdc/ttc_core_cex_39.json (branch claude/kind-lamport-y8fdme), copied to
                results/k4_haxell/ext/: k = 4 core counterexamples to OC/OC1
  B<, B>        k4/sdc/oc1_core_cex_verify.py (branch claude/kind-lamport-y8fdme): strict perturbations of TTC instance
                36 (k4/oc1_hall.md §16)
  PW(f,W,r)     k4/ksens/fam_ladder.clean (branch claude/k4-ksens): the clean PW family, k = max(r + 1, f + 1)"""
import os, json
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))


def rows(R):
    sets = [[g for g, x in enumerate(r) if x > 0] for r in R]
    vals = [[x for x in r if x > 0] for r in R]
    return sets, vals


def pw_clean(f, W, r):
    P = list(range(f)); Q = list(range(f, f + W)); D = list(range(f + W, f + W + r))
    sets = [[j] + D for j in range(f)] + [P + [Q[i]] for i in range(W)]
    vals = [[20] + [19 - t for t in range(r)] for j in range(f)] + [[2 * (f - j) for j in range(f)] + [1] for i in range(W)]
    return sets, vals, f + W + r


def named():
    out = []
    out.append(('PW5', [[0, 5, 6, 7, 8], [1, 5, 6, 7, 8], [2, 5, 6, 7, 8], [0, 1, 2, 3], [0, 1, 2, 4]],
                [[10, 9, 8, 7, 6]] * 3 + [[6, 4, 2, 1], [6, 4, 2, 1]], 9))
    out.append(('PW4', [[0, 5, 6, 7], [1, 5, 6, 7], [2, 5, 6, 7], [0, 1, 2, 3], [0, 1, 2, 4]],
                [[10, 9, 8, 7]] * 3 + [[6, 4, 2, 1], [6, 4, 2, 1]], 8))
    out.append(('RD5', [[0, 3, 4, 5, 1], [1, 2, 3], [1, 3, 4, 2], [0, 2, 6, 5]],
                [[26, 44, 24, 33, 57], [12, 11, 6], [9, 6, 1, 8], [36, 53, 4, 47]], 7))
    out.append(('RD4', [[0, 3, 5, 1], [1, 2, 3], [1, 3, 4, 2], [0, 2, 6, 5]],
                [[26, 44, 33, 57], [12, 11, 6], [9, 6, 1, 8], [36, 53, 4, 47]], 7))
    s, v = rows([[34, 0, 0, 0, 38, 35, 37, 33], [0, 10, 5, 0, 0, 4, 2, 0], [0, 2, 0, 0, 3, 0, 1, 0], [52, 54, 53, 4, 0, 0, 0, 51]])
    out.append(('KG8', s, v, 8))
    s, v = rows([[0, 155, 1, 0, 0, 155, 0], [0, 75, 2, 74, 0, 74, 77], [0, 0, 0, 2, 133, 0, 134], [1, 4, 0, 2, 0, 0, 0]])
    out.append(('KG7', s, v, 7))
    return out


def ttc():
    d = json.load(open(os.path.join(ROOT, 'results', 'k4_haxell', 'ext', 'ttc_core_cex_39.json')))
    return [('TTC%d' % t, x['sets'], x['vals'], 1 + max(max(s) for s in x['sets'])) for t, x in enumerate(d)]


def bcore():
    S = [[0, 2, 3, 1], [6, 4, 5, 9], [1, 2, 3, 9], [1, 6, 7, 8], [3, 6, 9], [1, 3, 6, 9]]
    return [('B<', S, [[6, 14, 16, 12], [4, 18, 12, 28], [28, 4, 16, 21], [16, 14, 12, 6], [28, 8, 24], [20, 30, 8, 4]], 10),
            ('B>', S, [[6, 14, 16, 12], [4, 18, 12, 28], [28, 4, 16, 19], [16, 14, 12, 6], [28, 8, 24], [20, 30, 8, 4]], 10)]


def pw_grid(fmax=5, wmax=4, rmax=8):
    out = []
    for f in range(2, fmax + 1):
        for W in range(1, wmax + 1):
            for r in range(2, rmax + 1):
                s, v, m = pw_clean(f, W, r)
                out.append(('PW(%d,%d,%d)' % (f, W, r), s, v, m))
    return out
