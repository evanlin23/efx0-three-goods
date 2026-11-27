"""The ladder test (k4/ksens.md §4): clean PW(f, W, r) instances (x_j: p_j worth 20, pool D worth 19, 18, ...; wanters:
p_1..p_f worth 2f, 2f - 2, ..., 2 and q worth 1, identical rankings) and the least number of improving chains after
which the natural order's picks extend (kchains.py), free and with one absorber.

    python3 k4/ksens/fam_ladder.py f W r CMAX [bfs]
(default: ocseq.py, c chains in one SAT call; bfs: kchains.py's breadth-first search)"""
import sys, json, time
import _paths
import kchains, ocseq


def clean(f, W, r):
    P = list(range(f)); Q = list(range(f, f + W)); D = list(range(f + W, f + W + r))
    sets = [[j] + D for j in range(f)] + [P + [Q[i]] for i in range(W)]
    vals = [[20] + [19 - t for t in range(r)] for j in range(f)] + [[2 * (f - j) for j in range(f)] + [1] for i in range(W)]
    return sets, vals, f + W + r


if __name__ == '__main__':
    f, W, r, cmax = map(int, sys.argv[1:5])
    sets, vals, m = clean(f, W, r); t0 = time.time()
    for A in (None, 1):
        if 'bfs' in sys.argv[5:]:
            c, info = kchains.min_chains(sets, vals, m, tuple(range(f + W)), cmax, A, cap=400000, log=True)
        else:
            c, info = ocseq.least(sets, vals, m, tuple(range(f + W)), cmax, A), {'method': 'ocseq'}
        print('PW(%d,%d,%d) k %d n %d m %d A %s: least chains %s %s %.0fs' % (f, W, r, max(r + 1, f + 1), f + W, m, A,
              c if c is not None else '> %d' % cmax, info, time.time() - t0), flush=True)
