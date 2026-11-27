"""Family POOL(f, r) (k4/ksens.md): f frozen agents x_1..x_f, each with its own wanter w_j, sharing a junk pool D of
r goods in which every pair is worth more to each x_j than its pick.  Agents 0..f-1 are the x_j (goods p_j = j, and
D), agents f..2f-1 the w_j (goods p_j and q_j = f + j).  D = goods 2f .. 2f + r - 1.  Order: x_1..x_f, w_1..w_f.

    python3 k4/ksens/fam_pool.py f r SEED [T]"""
import sys, json, random, time
import _paths
import ocsat


def make(f, r, rng):
    D = list(range(2 * f, 2 * f + r))
    sets = [[j] + D for j in range(f)] + [[j, f + j] for j in range(f)]
    vals = [[100] + rng.sample(range(51, 100), r) for j in range(f)] + [[100, 50] for j in range(f)]
    return sets, vals, 2 * f + r


if __name__ == '__main__':
    f, r, seed = map(int, sys.argv[1:4]); T = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    rng = random.Random(seed)
    for t in range(T):
        sets, vals, m = make(f, r, rng); n = 2 * f; t0 = time.time()
        O = ocsat.OC(sets, vals, m); Y = ocsat.sd(sets, vals, tuple(range(n)), m); b = ocsat.bases_of(Y, n)
        res = {'md': O.holds(b, md=True), 'ext': O.holds(b, chain='none'), 'ext1': O.holds(b, chain='none', A=1)}
        res['oc'] = res['ext'] or O.holds(b, chain='need')
        res['oc1'] = res['ext1'] or O.holds(b, chain='need', A=1)
        print('f', f, 'r', r, 'k', r + 1, 'n', n, 'm', m, res, json.dumps((sets, vals)) if not res['oc1'] else '', '%.1fs' % (time.time() - t0), flush=True)
        O.close()
