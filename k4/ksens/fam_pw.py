"""Family PW(f, W, r) (k4/ksens.md): f frozen agents x_j (goods p_j and a shared junk pool D of r goods, every pair of
D worth more to x_j than p_j), and W wanters w_i that each value every p_j above their own good q_i.  Goods: p_j = j,
q_i = f + i, D = f + W .. f + W + r - 1.  Order x_1..x_f, w_1..w_W: x_j picks p_j, w_i picks q_i.

    python3 k4/ksens/fam_pw.py f W r SEED T"""
import sys, json, random, time
import _paths
import ocsat


def make(f, W, r, rng):
    P = list(range(f)); Q = list(range(f, f + W)); D = list(range(f + W, f + W + r))
    sets = [[j] + D for j in range(f)] + [P + [Q[i]] for i in range(W)]
    vals = [[100] + rng.sample(range(51, 100), r) for j in range(f)]
    for i in range(W):
        pv = rng.sample(range(60, 100), f); vals.append(pv + [rng.randint(10, min(pv) - 1)])
    return sets, vals, f + W + r


def run(sets, vals, m, order):
    n = len(sets); O = ocsat.OC(sets, vals, m); Y = ocsat.sd(sets, vals, order, m); b = ocsat.bases_of(Y, n)
    res = {'md': O.holds(b, md=True), 'ext': O.holds(b, chain='none'), 'ext1': O.holds(b, chain='none', A=1)}
    res['oc'] = res['ext'] or O.holds(b, chain='need')
    res['oc1'] = res['ext1'] or O.holds(b, chain='need', A=1)
    O.close(); return Y, res


if __name__ == '__main__':
    f, W, r, seed, T = map(int, sys.argv[1:6]); rng = random.Random(seed); bad = {'oc': 0, 'oc1': 0, 'md': 0}
    t0 = time.time()
    for t in range(T):
        sets, vals, m = make(f, W, r, rng)
        Y, res = run(sets, vals, m, tuple(range(f + W)))
        for k in bad: bad[k] += not res[k]
        if not res['oc'] and bad['oc'] <= 2: print('  FAIL', res, json.dumps((sets, vals)), 'picks', Y, flush=True)
    print('PW f', f, 'W', W, 'r', r, 'k', max(r + 1, f + 1), 'n', f + W, 'm', f + W + r, 'T', T, 'failing', bad, '%.0fs' % (time.time() - t0), flush=True)
