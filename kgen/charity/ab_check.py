"""Lemma AB and Conjecture AB (kgen/charity.md §9): one-loser absorption along an envy path.

Move AB(pi): for an envy path s = u_0 -> u_1 -> ... -> u_r = a (r >= 1) from a source s of an EFX0 state X with strong
charity and pool P: u_0 takes X_{u_0} + X_{u_1}, u_i takes X_{u_{i+1}} (0 < i < r), a takes P.  Every agent but a is
weakly better off; the result is complete on P.  By Lemma AB it is EFX0 iff a strongly envies no bundle of the result
and nobody strongly envies X_{u_0} + X_{u_1}.  This script enumerates every envy path from a source (every simple path
of the acyclic envy graph, length >= 1) in each stranded state and reports whether some AB move gives a complete EFX0
allocation (checked with the raw definition).  Variant AB0: also allow a = s (r = 0): s takes X_s + P.

States: S'(sigma, 3) and S'(sigma, 4), the CH-F instances, and the states of ol_check.py (Pareto maxima, robust
CKMS stops and random charity states on the curated instances).

    python3 kgen/charity/ab_check.py SEED RUNS"""
import sys, random, collections, json
from chlib import Inst, from_sets, efx0, pool_ok, pool_of, envy_graph, sources, pm_with_pool, ckms
from stuck_family import build
import w_counterexample as WC


def ab_moves(I, X):
    G = envy_graph(I, X); S = sources(I, X, G); P = pool_of(I, X); out = []

    def paths(u, pth):
        yield pth
        for w in G[u]:
            if w not in pth:
                yield from paths(w, pth + [w])
    for s in S:
        for pth in paths(s, [s]):
            Y = [set(B) for B in X]
            if len(pth) == 1:
                Y[s] |= P
            else:
                Y[pth[0]] = X[pth[0]] | X[pth[1]]
                for i in range(1, len(pth) - 1):
                    Y[pth[i]] = set(X[pth[i + 1]])
                Y[pth[-1]] = set(P)
            assert not pool_of(I, Y)
            if efx0(I, Y):
                out.append(pth)
    return out


if __name__ == '__main__':
    seed, RUNS = map(int, sys.argv[1:3]); rng = random.Random(seed); C = collections.Counter()
    print('$ python3 kgen/charity/ab_check.py', *sys.argv[1:], flush=True)
    states = []
    for s in (2, 3, 4, 5):
        for k in (3, 4):
            I, X, P, src, ch = build(s, k, own=True); states.append(("S'(%d,%d)" % (s, k), I, X))
    states.append(('CH-F k4', Inst(9, 14, WC.V4), WC.X4)); states.append(('CH-F k3', Inst(12, 17, WC.V3), WC.X3))
    from ch_screen import load
    from ch_ckms import sd_start
    from ol_check import random_charity_state
    for name, sets, vals, m in load():
        I = from_sets(sets, vals, m)
        X, st = pm_with_pool(I, 1)
        if X is not None:
            states.append(('Pareto maximum ' + name, I, X))
        for r in range(RUNS):
            Xc, P, cnt, tab = ckms(I, X=None if r % 2 == 0 else sd_start(I, rng), rng=rng)
            if P:
                Xc, P, cnt, tab = ckms(I, X=Xc, rng=rng, mode='all')
            if P:
                states.append(('CKMS stop ' + name, I, Xc))
            Xr = random_charity_state(I, rng)
            if Xr is not None:
                states.append(('random charity state ' + name, I, Xr))
    for name, I, X in states:
        assert efx0(I, X) and pool_ok(I, X)
        mv = ab_moves(I, X)
        r1 = [p for p in mv if len(p) > 1]
        kind = name.split(' ')[0] if not name.startswith(('S\'', 'CH-F')) else 'family'
        kind = {'Pareto': 'Pareto maximum', 'CKMS': 'CKMS stop', 'random': 'random charity state'}.get(kind, kind)
        C['%s: an AB move completes %s' % (kind, bool(r1))] += 1
        C['%s: an AB or AB0 move completes %s' % (kind, bool(mv))] += 1
        if not mv:
            print('NO AB MOVE', name, json.dumps({'inst': I.to_json(), 'X': [sorted(B) for B in X]}), flush=True)
        elif name.startswith(("S'", 'CH-F')):
            print('%s: %d AB moves, e.g. path %s' % (name, len(mv), mv[0]), flush=True)
    for key in sorted(C):
        print(key, C[key])
