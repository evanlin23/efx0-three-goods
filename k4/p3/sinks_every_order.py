"""For every serial-dictatorship order (all orders for n <= 5, else --orders random ones), on (4, 3) instances (or all
k = 4 instances of the suite with --p=4): do the picks extend at all, and with at most B bundles of three or more goods
(B = 1, 2)? Counts pick vectors that extend but not with B big bundles, per instance; and instances where no order
extends with B big bundles although some order extends.
    python3 k4/p3/sinks_every_order.py suite|screen|cores|random [--n=6] [--count=100] [--orders=30] [--seed=1] [--p=4]
"""
import sys, os, random, json, time, collections, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p3lib import *
import dump_rules

if __name__ == '__main__':
    src = sys.argv[1]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[2:] if a.startswith('--'))
    rng = random.Random(int(opt.get('seed', 1))); K = int(opt.get('orders', 30))
    print('$ python3 k4/p3/sinks_every_order.py ' + ' '.join(sys.argv[1:]), flush=True)
    if opt.get('p') == '4':
        import p3lib
        L = [I for I in p3lib._suite() if I.p() >= 4]
    else:
        L = dump_rules.load(src, opt, rng)
    cnt = collections.Counter(); ex = collections.defaultdict(list); t0 = time.time()
    for I in L:
        C = Complete(I); bb = {B: C.big_bound(B) for B in (1, 2)}
        ords = list(itertools.permutations(range(I.n))) if I.n <= 5 else [tuple(rng.sample(range(I.n), I.n)) for _ in range(K)]
        seen = {}; anyB = collections.Counter()
        for o in ords:
            pk = tuple(sd(I, o))
            if pk in seen: continue
            fixed = {g: i for i, g in enumerate(pk) if g is not None}
            r = {None: C.solve(fixed=fixed) is not None}
            if r[None]:
                for B in (1, 2): r[B] = C.solve(fixed=fixed, extra=bb[B]) is not None
            seen[pk] = r
            cnt['pick vectors'] += 1; cnt['extend'] += r[None]
            for B in (1, 2):
                if r[None] and not r[B]:
                    cnt[f'extend, not with <= {B} big'] += 1; ex[B].append((I.n, I.m, I.name, o, pk, I.as_json()))
                if r[None] and r[B]: anyB[B] += 1
            anyB[None] += r[None]
        cnt['instances'] += 1
        for B in (None, 1, 2):
            if not anyB[B]: cnt[f'instances: no order extends' + (f' with <= {B} big' if B else '')] += 1
    print(dict(cnt), f'{time.time()-t0:.0f}s', flush=True)
    for B in (1, 2):
        if ex[B]:
            e = min(ex[B], key=lambda e: (e[0], e[1]))
            print(f'smallest: extends but not with <= {B} big: n={e[0]} m={e[1]} {e[2]} order {e[3]} picks {e[4]}')
            print('   ', json.dumps(e[5]))
