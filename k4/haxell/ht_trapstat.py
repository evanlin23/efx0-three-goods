"""Structure of the traps of G_1 (k4/haxell.md §4): for every trap found on SRC, the pooled goods' wanters (agents
valuing the good above their whole holding), the bundle sizes, and |R_i| of the agents involved.

    python3 k4/haxell/ht_trapstat.py SRC [NMAX=3] [MMAX=7]"""
import sys, collections, json
import multiprocessing as mpc
from ht_lib import Inst, happy_vec, bundles, instances
from ht_gstar import traps


def job(item):
    name, sets, vals, m = item
    I = Inst(sets, vals, m)
    S, comp, T = traps(I)
    out = []
    for s in T:
        X = bundles(I, list(s)); P = [g for g in range(m) if s[g] < 0]
        hold = [I.val(i, X[i]) for i in range(I.n)]
        wanters = {g: [i for i in range(I.n) if I.v[i].get(g, 0) > hold[i]] for g in P}
        out.append((name, sets, vals, X, P, wanters, [len(x) for x in X], [len(r) for r in I.R]))
    return out


if __name__ == '__main__':
    args = dict(a.split('=') for a in sys.argv[2:] if '=' in a)
    src = sys.argv[1]; nmax = int(args.get('NMAX', '3')); mmax = int(args.get('MMAX', '7'))
    print('$ python3 k4/haxell/ht_trapstat.py', *sys.argv[1:], flush=True)
    C = collections.Counter(); ex = []
    items = [it for it in instances(src) if len(it[1]) <= nmax and it[3] <= mmax]
    with mpc.Pool() as pool:
        for res in pool.imap_unordered(job, items):
            for name, sets, vals, X, P, W, sizes, ks in res:
                C['traps'] += 1
                C['pool size %d' % len(P)] += 1
                mw = max(len(w) for w in W.values())
                C['most wanters of a pooled good: %d' % mw] += 1
                C['bundle sizes %s' % sorted(sizes)] += 1
                C['some agent with 4 goods holds 2+ goods' ] += any(k == 4 and s >= 2 for k, s in zip(ks, sizes))
                if len(ex) < 6:
                    ex.append((name, sets, vals, X, P, W))
    for e in ex:
        print('TRAP', e[0], json.dumps((e[1], e[2])), 'bundles', e[3], 'pool', e[4], 'wanters', e[5])
    for k in sorted(C):
        print(k, C[k])
