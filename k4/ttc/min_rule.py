"""Least-gain chain rules (k4/ttc.md §4).  §29 of k4/sdc.md ranked the improving chains by the most junk or the largest
gain, and no such rule picks a repairing chain.  The YRMH-IGYT runs suggest the opposite direction: repairs are
"just enough" trades.  For every hard start (picks without a one-absorber completion), enumerate every improving chain
(de_free moves, chains only) and test whether the best-ranked chains under each rule repair (one-absorber completion):
  mintot   : the least total gain sum_i (v_i(new) - v_i(old)) over the chain agents
  minmax   : the least largest gain of a chain agent
  minrel   : the least total relative gain sum_i (v_i(new) - v_i(old)) / v_i(old)  (old = 0: counted as v_i(new))
  paretomin: chains whose new value vector is Pareto-minimal among the improving chains' vectors
  minagents: the fewest chain agents, then mintot
  minx0    : the least gain of x_0 (the pool requester), then mintot
For each rule: 'some' = some best-ranked chain repairs; 'every' = every best-ranked chain repairs (ties).

    python3 k4/ttc/min_rule.py SRC [N SEED] [nmax=5]"""
import sys, json, random, collections, time
from fractions import Fraction
import ttclib as T


def chain_feats(E, base, b2, desc):
    B = T.bundles(E, base); B2 = T.bundles(E, b2)
    kind, path, H = desc
    gains = {i: T.val(E, i, B2[i]) - T.val(E, i, B[i]) for i in path}
    rel = sum(Fraction(g, T.val(E, i, B[i])) if T.val(E, i, B[i]) > 0 else Fraction(T.val(E, i, B2[i]))
              for i, g in gains.items())
    vec = tuple(T.val(E, i, B2[i]) for i in range(E.n))
    return {'tot': sum(gains.values()), 'max': max(gains.values()), 'rel': rel, 'vec': vec, 't': len(path),
            'g0': gains[path[0]]}


RULES = {
    'mintot': lambda f: (f['tot'],),
    'minmax': lambda f: (f['max'], f['tot']),
    'minrel': lambda f: (f['rel'],),
    'minagents': lambda f: (f['t'], f['tot']),
    'minx0': lambda f: (f['g0'], f['tot']),
}


def main(argv):
    src = argv[0]; rest = argv[1:]
    N = int(rest[0]) if rest and rest[0].isdigit() else 0
    seed = int(rest[1]) if len(rest) > 1 and rest[1].isdigit() else 0
    kw = dict(a.split('=', 1) for a in rest if '=' in a); nmax = int(kw.get('nmax', '5'))
    print('$ python3 k4/ttc/min_rule.py', *argv, flush=True)
    t0 = time.time(); C = collections.Counter(); rng = random.Random(seed + 7); ex = collections.defaultdict(list)
    for name, sets, vals, m in T.load_items(src, N, seed):
        n = len(sets)
        if n > nmax:
            continue
        E = T.Enc(sets, vals, m); seen = set()
        for pi in T.orders_of(n, rng):
            Y = tuple(T.sd(E, pi)[0])
            if Y in seen:
                continue
            seen.add(Y); base = T.base_of(E, Y)
            if T.extends_A(E, base, 1):
                continue
            C['distinct hard starts'] += 1
            feats = []
            for b2, ds in T.DF.moves(E, base, describe=True, all_desc=True).items():
                f = min((chain_feats(E, base, b2, d) for d in ds), key=lambda f: (f['tot'], f['t']))
                feats.append((f, b2))
            ok = {b2: T.extends_A(E, b2, 1) for _, b2 in feats}
            C['repairing chains exist'] += any(ok.values())
            for rn, key in RULES.items():
                best = min(key(f) for f, _ in feats)
                tied = [b2 for f, b2 in feats if key(f) == best]
                C[rn + ': some'] += any(ok[b] for b in tied)
                C[rn + ': every'] += all(ok[b] for b in tied)
                if not any(ok[b] for b in tied) and len(ex[rn]) < 2:
                    ex[rn].append((name, Y))
            vecs = [f['vec'] for f, _ in feats]
            pm = [b2 for f, b2 in feats if not any(all(w[i] <= f['vec'][i] for i in range(n)) and w != f['vec']
                                                     for w in vecs)]
            C['paretomin: some'] += any(ok[b] for b in pm)
            C['paretomin: every'] += all(ok[b] for b in pm)
            C['paretomin: count'] += len(pm); C['chains: count'] += len(feats)
    for k in sorted(C):
        print(k, C[k])
    for rn, l in ex.items():
        print('no repair among the best of', rn, l)
    print('time %.0f s' % (time.time() - t0), flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
