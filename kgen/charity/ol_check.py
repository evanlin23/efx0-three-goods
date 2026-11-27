"""Conjecture OL (kgen/charity.md §9): from a stranded state X (EFX0 with strong charity), some complete EFX0
allocation leaves at most one agent worse off than in X.  Tested on
  (a) every Pareto maximum with a nonempty pool found on the 168 curated k = 4 instances (chlib.pm_with_pool),
  (b) robust CKMS stopping states with a nonempty pool on the curated instances (several runs each),
  (c) random EFX0 states with strong charity and a nonempty pool (SAT with random phases) on the curated instances,
      a weaker hypothesis than (a) and (b),
reporting the fewest losers (losers.fewest_losers) per state.

    python3 kgen/charity/ol_check.py SEED RUNS [screen|rand<K>]"""
import sys, random, collections, json
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from chlib import from_sets, pm_with_pool, ckms, pool_of, efx0, pool_ok, Enc
from ch_screen import load
from ch_ckms import sd_start
from losers import fewest_losers


def random_charity_state(I, rng, minpool=1):
    E = Enc(I, strong=True)
    pool = [E.x[g][I.n] for g in range(I.m)]
    c = CardEnc.atleast(lits=pool, bound=minpool, top_id=E.top, encoding=EncType.seqcounter)
    s = Cadical153(bootstrap_with=E.cl + c.clauses)
    s.set_phases([v if rng.random() < 0.5 else -v for v in range(1, E.top + 1)])
    ok = s.solve(); X = E.decode(s.get_model()) if ok else None; s.delete()
    return X


if __name__ == '__main__':
    seed, RUNS = map(int, sys.argv[1:3]); rng = random.Random(seed); C = collections.Counter()
    print('$ python3 kgen/charity/ol_check.py', *sys.argv[1:], flush=True)
    src = sys.argv[3] if len(sys.argv) > 3 else 'screen'
    if src == 'screen':
        insts = [(name, from_sets(sets, vals, m)) for name, sets, vals, m in load()]
    else:                                   # 'rand<K>': random instances, n = 3..6, agents value 2..K goods
        from chlib import rand_inst
        K = int(src[4:])
        insts = [('rand#%d' % t, rand_inst(rng, n, rng.randint(n + 1, 2 * n + 2), 2, K, vmax=12))
                 for t, n in enumerate([rng.randint(3, 6) for _ in range(150)])]
    for name, I in insts:
        states = []
        X, st = pm_with_pool(I, 1)
        if X is not None:
            states.append(('Pareto maximum', X))
        for r in range(RUNS):
            Xc, P, cnt, tab = ckms(I, X=None if r % 2 == 0 else sd_start(I, rng), rng=rng)
            if P:
                Xc, P, cnt, tab = ckms(I, X=Xc, rng=rng, mode='all')
            if P:
                states.append(('CKMS stop', Xc))
        for r in range(RUNS):
            Xr = random_charity_state(I, rng)
            if Xr is not None:
                states.append(('random charity state', Xr))
        for kind, X in states:
            assert efx0(I, X) and pool_ok(I, X)
            k, L, Y = fewest_losers(I, X)
            C['%s: fewest losers %s' % (kind, k)] += 1
            if k is None or k >= 2:
                print('LOSERS', k, name, kind, json.dumps({'X': [sorted(B) for B in X],
                                                           'pool': sorted(pool_of(I, X))}), flush=True)
    for key in sorted(C):
        print(key, C[key])
