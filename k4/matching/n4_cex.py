"""The 11 n = 4 OC1^max counterexamples (compute/k4-oc1max-cert; results/k4_matching/data/oc1max_cex_n4.json is
results/k4_oc1max/oc1max_cex_n4.json of that branch at cfb3c18) under the matching view (k4/matching.md §5).

For each stored perfect start: the free-slot deficiency delta_oa (per owner), the least delta_oa one official move
reaches, the least exchange excess d_o - s_o over every chain from a dangerous agent, improving H0 and owner
(exchange.ex_value), and over the first moves: the least delta_oa reached by a second move (OC2 = 0).

    python3 k4/matching/n4_cex.py"""
import os, json, collections
import _mpaths  # noqa: F401
from mlib import M, INF, subsets
from exchange import general_chains, apply_chain, ex_value


def best_exchange(I, base):
    J = I.junk(base); fz = set(I.frozen(base)); Y = [b[0] if b else None for b in base]; best = (INF, None); C = collections.Counter()
    for P, Hs in general_chains(I, base):
        k, xt = P[0], P[-1]; used = set(g for h in Hs.values() for g in h)
        Pi = [g for g in J if g not in used] + [Y[xt]]
        for H0 in subsets([g for g in Pi if g in I.R[k]], 1):
            if I.V(k, H0) <= I.V(k, base[k]) or (xt in fz and Y[xt] not in H0): continue
            Bp = apply_chain(I, base, P, list(H0), Hs)
            for o in range(I.n):
                d, s, why, _ = ex_value(I, base, P, Bp, o)
                C[why if d >= INF else 'finite'] += 1
                if d < INF and d - s < best[0]: best = (d - s, (P, list(H0), {i: h for i, h in Hs.items() if h}, o))
    return best, C


if __name__ == '__main__':
    D = json.load(open(os.path.join(_mpaths.ROOT, 'results', 'k4_matching', 'data', 'oc1max_cex_n4.json')))['instances']
    print('$ python3 k4/matching/n4_cex.py   (%d instances)' % len(D), flush=True)
    T = collections.Counter()
    for t, d in enumerate(D):
        I = M(d['sets'], d['vals']); Y = d['picks']; base = [[g] for g in Y]
        dl = I.deficiency(base, 'oa'); own = I.owner_deficiency(base, 'oa')
        mv = I.moves(base); after = [I.deficiency(b, 'oa', dmax=dl) for b in mv]
        (ex, arg), C = best_exchange(I, base)
        two = min(min([I.deficiency(b2, 'oa', dmax=1) for b2 in I.moves(b)] or [INF]) for b in mv)
        print('instance %d' % t, json.dumps([d['sets'], d['vals']]), 'picks', Y, '| J', I.junk(base), 'frozen',
              I.frozen(base), 'D', I.dangerous(base))
        print('   delta_oa', dl, 'per owner', own, '| least delta after one move', min(after),
              '| least exchange excess d - s', ex, 'at (P, H0, Hs, owner) =', arg, '|', dict(C),
              '| least delta after two moves', two)
        T['delta %d, after one move %d, exchange excess %s, after two moves %d' % (dl, min(after), ex, two)] += 1
    for k in sorted(T): print(k, T[k])
