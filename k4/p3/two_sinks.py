"""Conjecture TS (two sinks; k4/p3.md section 4): the picks of LB4's Phase 1 (index insertion; no upgrades, no
rotations) extend to an EFX0 allocation with at most two bundles of three or more goods.
For each instance: do the Phase 1 picks extend at all, with <= 1 big bundle, with <= 2 big bundles (SAT, raw EFX0
re-check of every model). Instance sets as in k4/p3/dump_rules.py; --p=4 keeps instances with goods of 4+ valuers too.
    python3 k4/p3/two_sinks.py suite|screen|cores|random [--n=6] [--count=100] [--seed=1] [--orders=0] [--p=3]
--orders=K also tries K random insertion sequences per instance (counts instances where some sequence works).
"""
import sys, os, random, json, time, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p3lib import *
import dump_rules

def check(I, C, pk, B):
    fixed = {g: i for i, g in enumerate(pk) if g is not None}
    own = C.solve(fixed=fixed, extra=C.big_bound(B) if B is not None else ())
    if own is not None: assert efx0(I, bundles(I, own))
    return own

if __name__ == '__main__':
    src = sys.argv[1]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[2:] if a.startswith('--'))
    rng = random.Random(int(opt.get('seed', 1)))
    print('$ python3 k4/p3/two_sinks.py ' + ' '.join(sys.argv[1:]), flush=True)
    if opt.get('p') == '4' and src in ('suite', 'screen'):
        import p3lib
        L = p3lib._suite() if src == 'suite' else None
    else:
        L = dump_rules.load(src, opt, rng)
    cnt = collections.Counter(); ex = collections.defaultdict(list); t0 = time.time()
    for I in L:
        C = Complete(I)
        pk, order = phase1(I)
        r = {B: check(I, C, pk, B) is not None for B in (None, 1, 2)}
        cnt['instances'] += 1
        for B, ok in r.items():
            if not ok:
                cnt[f'fail <= {B} big'] += 1; ex[B].append((I.n, I.m, I.name, pk, I.as_json()))
        if not r[2] and int(opt.get('orders', 0)):
            for _ in range(int(opt['orders'])):
                tau = [rng.randrange(I.n) for _ in range(I.n)]
                if check(I, C, phase1(I, tau)[0], 2) is not None:
                    cnt['rescued by another insertion sequence'] += 1; break
    print(dict(cnt), f'{time.time()-t0:.0f}s', flush=True)
    for B in (None, 1, 2):
        if ex[B]:
            e = min(ex[B], key=lambda e: (e[0], e[1]))
            print(f'smallest failure (<= {B} big): n={e[0]} m={e[1]} {e[2]} picks {e[3]}')
            print('   ', json.dumps(e[4]))
