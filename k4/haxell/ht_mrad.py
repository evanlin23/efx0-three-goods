"""Augmentation radius in local moves (k4/haxell.md §3.5): for a partial EFX0 allocation s with a nonempty pool, the
fewest generic local moves (move one good to an agent, swap two holders, trade two bundles; intermediate states
arbitrary, the pool never growing) after which the state is a partial EFX0 allocation with a smaller pool.  Computed
for the states whose Hamming radius (ht_aug.py) exceeds HMIN, on the instances of SRC.

    python3 k4/haxell/ht_mrad.py SRC [NMAX=3] [MMAX=6] [HMIN=3] [DMAX=4]"""
import sys, itertools, collections, json, time
import multiprocessing as mpc
from functools import partial
from ht_lib import Inst, happy_vec, bundles, instances
from ht_aug import radius


def one(I, o):
    n, m = I.n, I.m
    for g in range(m):
        for b in range(n):
            if b != o[g]:
                t = list(o); t[g] = b; yield tuple(t)
    for g, h in itertools.combinations(range(m), 2):
        if o[g] != o[h]:
            t = list(o); t[g], t[h] = o[h], o[g]; yield tuple(t)
    for a, b in itertools.combinations(range(n), 2):
        yield tuple(b if x == a else a if x == b else x for x in o)


def mrad(I, s, dmax):
    p = s.count(-1); frontier = {s}; seen = {s}
    for d in range(1, dmax + 1):
        nxt = set()
        for o in frontier:
            for t in one(I, o):
                if t in seen or t.count(-1) > p:
                    continue
                if t.count(-1) < p and all(happy_vec(I, t)):
                    return d
                seen.add(t); nxt.add(t)
        frontier = nxt
    return None


def job(item, hmin, dmax):
    name, sets, vals, m = item
    I = Inst(sets, vals, m)
    out = collections.Counter(); worst = None
    for own in itertools.product(range(-1, I.n), repeat=m):
        if -1 not in own or not all(happy_vec(I, own)):
            continue
        h, _ = radius(I, own, 6)
        if h is not None and h <= hmin:
            continue
        r = mrad(I, own, dmax)
        out[(h, r)] += 1
        if worst is None or (r or 99) > (worst[0] or 99):
            worst = (r, h, own)
    return name, sets, vals, out, worst


if __name__ == '__main__':
    args = dict(a.split('=') for a in sys.argv[2:] if '=' in a)
    src = sys.argv[1]; nmax = int(args.get('NMAX', '3')); mmax = int(args.get('MMAX', '6'))
    hmin = int(args.get('HMIN', '3')); dmax = int(args.get('DMAX', '4'))
    print('$ python3 k4/haxell/ht_mrad.py', *sys.argv[1:], flush=True)
    t0 = time.time(); C = collections.Counter(); W = []
    items = [it for it in instances(src) if len(it[1]) <= nmax and it[3] <= mmax]
    with mpc.Pool() as pool:
        for name, sets, vals, out, worst in pool.imap_unordered(partial(job, hmin=hmin, dmax=dmax), items):
            for (h, r), c in out.items():
                C['states with Hamming radius %s and move radius %s' % (h if h is not None else '>6', r if r is not None else '>%d' % dmax)] += c
            if worst:
                W.append((worst[0] if worst[0] is not None else 99, name, sets, vals, worst))
    W.sort(key=lambda x: -x[0])
    for r, name, sets, vals, worst in W[:3]:
        I = Inst(sets, vals, 1 + max(max(s) for s in sets))
        print('WORST move radius', worst[0], 'Hamming', worst[1], name, json.dumps((sets, vals)), bundles(I, list(worst[2])),
              'pool', [g for g, a in enumerate(worst[2]) if a < 0], flush=True)
    for k in sorted(C):
        print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
