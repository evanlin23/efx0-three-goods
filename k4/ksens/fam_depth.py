"""Depth-two composition of RD5's mechanism, against two rounds of disjoint chains (k4/ksens.md §6, §8).

RD5 (refute_rd_k5.py): agent 0 must repair with {3, 4}, the picks of agents 1 and 2, which one round cannot collect.
Here agent 2 (holder of good 4) can only move by collecting two foreign picks c, c' itself:
  agent 2 values 4 (its pick) at E and c, c' at slightly more than E/2 each;
  C (holder of c) gains only from x, the pick of X, which gains only from two junk goods of its own;
  C' (holder of c') gains only from u, the pick of U, which gains only from two junk goods of its own.
So releasing c' takes a round (U -> C'), releasing 4 another (X -> C -> agent 2, which takes c from its predecessor and
c' from the junk), and agent 0 collects 4 in a third, unless something shortcuts it.  Variants: whether agent 2 keeps
its RD5 values for goods 1, 2, 3 ('keep'), and the values.

    python3 k4/ksens/fam_depth.py"""
import json, time
import _paths
import ocsat, ocseq


def make(keep):
    A = [[0, 3, 4, 5, 1], [26, 44, 24, 33, 57]]
    Y = [[0, 2, 6, 5], [36, 53, 4, 47]]
    B1 = [[1, 2, 3], [12, 11, 6]]
    # goods: c = 7, c' = 8, x = 9, u = 10, X's junk 11, 12, U's junk 13, 14
    B2 = [[4, 7, 8] + ([1, 2, 3] if keep else []), [20, 11, 11] + ([9, 8, 6] if keep else [])]
    C = [[7, 9], [10, 11]]; X = [[9, 11, 12], [10, 6, 6]]
    C2 = [[8, 10], [10, 11]]; U = [[10, 13, 14], [10, 6, 7]]
    agents = [A, B1, B2, Y, C, X, C2, U]          # 0 A, 1 B1, 2 B2, 3 Y, 4 C, 5 X, 6 C', 7 U
    return [a[0] for a in agents], [a[1] for a in agents], 15


if __name__ == '__main__':
    print('$ python3 k4/ksens/fam_depth.py', flush=True)
    order = (0, 3, 1, 2, 5, 4, 7, 6)
    for keep in (True, False):
        sets, vals, m = make(keep); n = len(sets); t0 = time.time()
        Y = ocsat.sd(sets, vals, order, m); b = ocsat.bases_of(Y, n)
        Q = ocseq.Seq(sets, vals, m); O = ocsat.OC(sets, vals, m)
        res = {'picks extend (A=1)': O.holds(b, chain='none', A=1)}
        for c in (1, 2, 3):
            res['%d round(s) (A=1)' % c] = Q.holds(b, c, 1, multi=True)
            if res['%d round(s) (A=1)' % c]: break
        res['one chain (A=1)'] = O.holds(b, chain='any', A=1); res['md'] = O.holds(b, md=True)
        print('keep %s: k %d n %d m %d order %s picks %s junk %s' % (keep, max(map(len, sets)), n, m, order, Y,
              [g for g in range(m) if g not in Y]), res, '%.0fs' % (time.time() - t0), json.dumps((sets, vals)), flush=True)
        O.close(); Q.close()
