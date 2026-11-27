"""Claim X, the uncoupled case of Theorem A2 (k4/p3.md section 5): in the Phase 1 state (index insertion, no upgrade),
if two free agents o1, o2 have picks that no frozen agent values, then the bases extend to an EFX0 allocation in which
every agent other than o1, o2 holds at most two goods (SAT; no rotation). Tests every such pair; reports states where
some uncoupled pair exists but none works, and states where some uncoupled pair fails.
    python3 k4/p3/claim_x.py SRC [--mutual=1] [options of k4/p3/dump_rules.py]
--mutual=1 tests Claim X' (also: neither owner values the other's pick).
"""
import sys, os, random, collections, json, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p3lib import *
import ts, dump_rules

if __name__ == '__main__':
    src = sys.argv[1]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[2:] if a.startswith('--'))
    rng = random.Random(int(opt.get('seed', 1)))
    print('$ python3 k4/p3/claim_x.py ' + ' '.join(sys.argv[1:]), flush=True)
    L = dump_rules.load(src, opt, rng)
    cnt = collections.Counter(); ex = []
    for I in L:
        s = ts.initial(I)[0]; fr = s.frozen()
        free = [i for i in range(I.n) if not fr[i]]
        frozen_goods = set().union(*(I.R[x] for x in range(I.n) if fr[x])) if any(fr) else set()
        unc = [o for o in free if not (s.base[o] & frozen_goods)]
        pairs = list(itertools.combinations(unc, 2))
        if opt.get('mutual'):     # Claim X': the owners' picks are not valued by the other owner either
            pairs = [(a, b) for a, b in pairs if not (s.base[a] & I.R[b]) and not (s.base[b] & I.R[a])]
        if not pairs: cnt['no uncoupled pair'] += 1; continue
        C = Complete(I); fixed = {g: i for i in range(I.n) for g in s.base[i]}
        res = []
        for o1, o2 in pairs:
            own = C.solve(fixed=fixed, extra=small_bound(C, [a for a in range(I.n) if a not in (o1, o2)]))
            if own is not None: assert efx0(I, bundles(I, own))
            res.append(own is not None)
        cnt['uncoupled pairs exist: ' + ('all work' if all(res) else 'some work' if any(res) else 'NONE WORKS')] += 1
        if not all(res): ex.append((I.n, I.m, I.name, [p for p, r in zip(pairs, res) if not r], I.as_json(), [sorted(b) for b in s.base]))
    for k, v in sorted(cnt.items()): print(f'  {k}: {v}')
    ex.sort(key=lambda e: (e[0], e[1]))
    for e in ex[:3]:
        print(f'  failing uncoupled pairs in {e[2]} (n={e[0]}, m={e[1]}): {e[3]}; bases {e[5]}')
        print('     ', json.dumps(e[4]))
