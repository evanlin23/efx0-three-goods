"""Do the picks of EVERY serial-dictatorship order extend to an EFX0 allocation, on (k, p) = (4, 3) instances?
(At k = 4 in general not every order works: k4/sdc.md, K4.SDC.SEL.)  For each instance and each order (all orders for
n <= 6, else --orders random ones), SAT with the picks fixed. Prints every failing (instance, order) and totals.
    python3 k4/p3/every_order.py suite|screen|cores|random [--n=6] [--count=200] [--orders=50] [--seed=1]
"""
import sys, os, random, itertools, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p3lib import *

def orders(I, rng, K):
    if I.n <= 6:
        return list(itertools.permutations(range(I.n)))
    return [tuple(rng.sample(range(I.n), I.n)) for _ in range(K)]

def run(I, rng, K, out):
    C = Complete(I); bad = 0; tot = 0
    cache = {}
    for o in orders(I, rng, K):
        pk = sd(I, o)
        key = tuple(pk)
        if key not in cache:
            cache[key] = C.solve(fixed={g: i for i, g in enumerate(pk) if g is not None})
        tot += 1
        if cache[key] is None:
            bad += 1
            if bad <= 2: out.append({'inst': I.as_json(), 'order': o, 'picks': pk})
    return tot, bad, len(cache)

if __name__ == '__main__':
    src = sys.argv[1]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[2:] if a.startswith('--'))
    rng = random.Random(int(opt.get('seed', 1))); K = int(opt.get('orders', 50))
    print('$ python3 k4/p3/every_order.py ' + ' '.join(sys.argv[1:]), flush=True)
    if src == 'suite': L = suite_p3()
    elif src == 'screen': L = screen_p3()
    elif src == 'cores':
        L = []
        for f in core_lists_p3():
            cs = cores_from(f); rng.shuffle(cs)
            for m, sets in cs[:int(opt.get('count', 50))]:
                L.append(Inst(sets, random_types(rng, sets, m), m, os.path.basename(f)))
    else:
        L = []
        for t in range(int(opt.get('count', 200))):
            rc = random_core43(rng, int(opt.get('n', 6)))
            if rc: L.append(Inst(rc[1], random_types(rng, rc[1], rc[0]), rc[0], f'rand{t}'))
    T = B = Ib = 0; ex = []; t0 = time.time()
    for I in L:
        tot, bad, npk = run(I, rng, K, ex)
        T += tot; B += bad; Ib += bad > 0
        if bad: print(f'FAIL {I.name} n={I.n} m={I.m}: {bad}/{tot} orders fail ({npk} distinct pick vectors)', flush=True)
    print(f'instances {len(L)}, orders {T}, failing orders {B}, instances with a failing order {Ib}, {time.time()-t0:.0f}s')
    for e in ex[:6]: print('EX', json.dumps(e))
