"""Family PWQ(f, W, r) against one round of disjoint chains (k4/ksens.md §6): PW(f, W, r) (k4/ksens.md §1) where the
frozen agents also value the wanters' own goods q_i like pool goods, so a repair, which moves a wanter from q_i to a
pick, releases q_i into the pool.  Tests, from the natural order: one chain, one round (free and one absorber), MD.

    python3 k4/ksens/fam_pwq.py f W r SEED T"""
import sys, json, random, time
import _paths
import ocsat


def make(f, W, r, rng, clean=False):
    P = list(range(f)); Q = list(range(f, f + W)); D = list(range(f + W, f + W + r))
    sets, vals = [], []
    for j in range(f):
        sets.append([j] + D + Q)
        vals.append([40] + ([38 - 2 * t for t in range(r + W)] if clean else rng.sample(range(21, 40), r + W)))
    for i in range(W):
        pv = [4 * (f - j) for j in range(f)] if clean else rng.sample(range(3, 30), f)
        sets.append(P + [Q[i]]); vals.append(pv + [1 if clean else rng.randint(1, min(pv) - 1) if min(pv) > 1 else 1])
    return sets, vals, f + W + r


if __name__ == '__main__':
    f, W, r, seed, T = map(int, sys.argv[1:6]); rng = random.Random(seed); n = f + W
    bad = {'one chain': 0, 'one round (free)': 0, 'one round (A=1)': 0, 'md': 0}; t0 = time.time()
    for t in range(T):
        sets, vals, m = make(f, W, r, rng, clean=(t == 0))
        O = ocsat.OC(sets, vals, m); Y = ocsat.sd(sets, vals, tuple(range(n)), m); b = ocsat.bases_of(Y, n)
        res = {'one chain': O.holds(b, chain='any', A=1), 'one round (free)': O.holds(b, chain='any', multi=True),
               'one round (A=1)': O.holds(b, chain='any', A=1, multi=True), 'md': O.holds(b, md=True)}
        for k in bad: bad[k] += not res[k]
        if not res['one round (free)'] or not res['md']:
            print('  ROUND FAILS', res, json.dumps((sets, vals)), 'picks', Y, flush=True)
        O.close()
    print('PWQ f %d W %d r %d: k %d n %d m %d, T %d, failing %s, %.0fs' % (f, W, r, r + W + 1, n, f + W + r, T, bad, time.time() - t0), flush=True)
