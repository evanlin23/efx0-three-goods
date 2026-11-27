"""Gadgets against one round of disjoint chains (k4/ksens.md §6, attempts/k4-ksens-round-gadgets.md): PW-type
instances with one or two wanters whose rankings over the frozen picks are chosen so that one wanter must trade up
several times (an agent moving twice), from the natural order.  Compares one chain, one round, two sequential chains
(ocseq), and MD.

    python3 k4/ksens/round_gadgets.py"""
import itertools, json
import _paths
import ocsat, ocseq


def make(f, W, r, ranks):
    """x_j: p_j (40) and pool D (r goods, 38, 36, ...); wanter i values p_j at 4 * ranks[i][j] + 4 and q_i at 2"""
    P = list(range(f)); Q = list(range(f, f + W)); D = list(range(f + W, f + W + r))
    sets = [[j] + D for j in range(f)]; vals = [[40] + [38 - 2 * t for t in range(r)] for j in range(f)]
    for i in range(W):
        sets.append(P + [Q[i]]); vals.append([4 * ranks[i][j] + 4 for j in range(f)] + [2])
    return sets, vals, f + W + r


if __name__ == '__main__':
    print('$ python3 k4/ksens/round_gadgets.py', flush=True)
    seen = 0
    for f, W, r in [(3, 1, 4), (3, 1, 5), (4, 1, 5), (3, 2, 4), (4, 2, 5), (4, 2, 6)]:
        for ranks in itertools.product(itertools.permutations(range(f)), repeat=W):
            sets, vals, m = make(f, W, r, ranks); n = f + W
            O = ocsat.OC(sets, vals, m); Q = ocseq.Seq(sets, vals, m)
            Y = ocsat.sd(sets, vals, tuple(range(n)), m); b = ocsat.bases_of(Y, n)
            res = {'ext': O.holds(b, chain='none', A=1), 'chain': O.holds(b, chain='any', A=1),
                   'round': O.holds(b, chain='any', A=1, multi=True), 'two chains': Q.holds(b, 2, 1), 'md': O.holds(b, md=True)}
            O.close(); Q.close()
            key = (f, W, r, tuple(sorted(res.items())))
            if not res['round'] or (res['two chains'] and not res['chain']):
                print('PW(%d,%d,%d) ranks %s: %s %s' % (f, W, r, ranks, res, json.dumps((sets, vals)) if not res['round'] else ''), flush=True)
            seen += 1
    print('configurations', seen)
