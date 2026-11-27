"""Family CW(f, r) (k4/ksens.md): complete want.  Hot goods p_1 > ... > p_f ranked the same way by everybody who
values them; agent x_j (j = 1..f) values p_1..p_j and a shared junk pool D of r goods (each worth more than half of
x_j's value for p_1); the last agent u values every p_j and its own good u_0.  Order x_1, ..., x_f, u: x_j picks p_j,
and every p_j is wanted by every later agent, so x_1..x_f are frozen.

    python3 k4/ksens/fam_cw.py f r SEED T [uD]     (uD: u values D too)"""
import sys, json, random, time
import _paths
import ocsat


def make(f, r, rng, uD=False):
    P = list(range(f)); u0 = f; D = list(range(f + 1, f + 1 + r))
    sets, vals = [], []
    for j in range(f):
        hv = sorted(rng.sample(range(80, 120), j + 1), reverse=True)     # values of p_1 .. p_{j+1}
        dv = rng.sample(range(hv[0] // 2 + 1, hv[-1]), r)
        sets.append(P[:j + 1] + D); vals.append(hv + dv)
    hv = sorted(rng.sample(range(80, 120), f), reverse=True)
    S = P + [u0]; V = hv + [rng.randint(10, 70)]
    if uD:
        S += D; V += rng.sample(range(1, V[-1]), r)
    sets.append(S); vals.append(V)
    return sets, vals, f + 1 + r


def run(sets, vals, m, order):
    n = len(sets); O = ocsat.OC(sets, vals, m); Y = ocsat.sd(sets, vals, order, m); b = ocsat.bases_of(Y, n)
    res = {'md': O.holds(b, md=True), 'ext': O.holds(b, chain='none'), 'ext1': O.holds(b, chain='none', A=1)}
    res['oc'] = res['ext'] or O.holds(b, chain='need')
    res['oc1'] = res['ext1'] or O.holds(b, chain='need', A=1)
    O.close(); return Y, res


if __name__ == '__main__':
    f, r, seed, T = map(int, sys.argv[1:5]); uD = 'uD' in sys.argv[5:]
    rng = random.Random(seed); bad = {'oc': 0, 'oc1': 0, 'md': 0}
    for t in range(T):
        sets, vals, m = make(f, r, rng, uD)
        Y, res = run(sets, vals, m, tuple(range(f + 1)))
        for k in bad: bad[k] += not res[k]
        if not res['oc1'] and bad['oc1'] <= 2: print('  FAIL', res, json.dumps((sets, vals)), 'picks', Y, flush=True)
    print('CW f', f, 'r', r, 'k', f + r, 'n', f + 1, 'T', T, 'failing', bad, flush=True)
