"""Augmentation radius of partial EFX0 allocations (k4/haxell.md §3.5).

For a partial EFX0 allocation s (every agent happy with respect to the allocated bundles) with a nonempty pool,
r(s) is the least number of goods whose holder changes (a pooled good placed counts; nothing returns to the pool)
in a partial EFX0 allocation t with fewer pooled goods.  An alternating tree whose collapse reassigns at most r goods
can augment s only if r(s) <= r.  The statement
    AUG_r:  every partial EFX0 allocation with a nonempty pool has r(s) <= r
would give EFX0 existence by induction on the pool (start from the empty allocation), with no potential.
This script computes r(s) exactly (by increasing d, all reassignments of d goods) for every partial EFX0 allocation
of each instance, up to DMAX, and reports the distribution and the worst states.

    python3 k4/haxell/ht_aug.py SRC [NMAX=4] [MMAX=7] [DMAX=4] [SHOW=4]"""
import sys, os, json, itertools, collections, time
from ht_lib import Inst, happy_vec, bundles, instances


def radius(I, s, dmax):
    n, m = I.n, I.m
    pool = s.count(-1)
    for d in range(1, dmax + 1):
        for G in itertools.combinations(range(m), d):
            choices = [[b for b in range(n) if b != s[g]] for g in G]
            for targets in itertools.product(*choices):
                o = list(s)
                for g, b in zip(G, targets):
                    o[g] = b
                if o.count(-1) < pool and all(happy_vec(I, o)):
                    return d, o
    return None, None


def job(item, dmax):
    name, sets, vals, m = item
    I = Inst(sets, vals, m, name)
    dist = collections.Counter(); worst = (0, None, None)
    for own in itertools.product(range(-1, I.n), repeat=m):
        if -1 not in own or not all(happy_vec(I, own)):
            continue
        d, t = radius(I, own, dmax)
        key = d if d is not None else 'more than %d' % dmax
        dist[key] += 1
        dd = d if d is not None else dmax + 1
        if dd > worst[0]:
            worst = (dd, own, t)
    return name, sets, vals, dist, worst


if __name__ == '__main__':
    import multiprocessing as mpc
    from functools import partial
    args = dict(a.split('=') for a in sys.argv[2:] if '=' in a)
    src = sys.argv[1]; nmax = int(args.get('NMAX', '4')); mmax = int(args.get('MMAX', '7'))
    dmax = int(args.get('DMAX', '4')); show = int(args.get('SHOW', '4'))
    print('$ python3 k4/haxell/ht_aug.py', *sys.argv[1:], flush=True)
    t0 = time.time(); C = collections.Counter(); W = collections.Counter(); shown = 0
    items = [it for it in instances(src) if len(it[1]) <= nmax and it[3] <= mmax]
    best = []
    with mpc.Pool(os.cpu_count()) as pool:
        for name, sets, vals, dist, worst in pool.imap_unordered(partial(job, dmax=dmax), items):
            C['instances'] += 1
            for k, v in dist.items():
                C['states with radius %s' % k] += v
            W['instances whose worst radius is %s' % (worst[0] if worst[0] <= dmax else 'more than %d' % dmax)] += 1
            best.append((worst[0], name, sets, vals, worst[1], worst[2]))
    best.sort(key=lambda x: -x[0])
    for w, name, sets, vals, s, t in best[:show]:
        I = Inst(sets, vals, 1 + max(max(x) for x in sets))
        print('WORST radius', w if w <= dmax else '> %d' % dmax, name, json.dumps((sets, vals)), 'state',
              bundles(I, list(s)), 'pool', [g for g in range(len(s)) if s[g] < 0],
              'augmented to', bundles(I, list(t)) if t else None, flush=True)
    for k in sorted(C, key=str):
        print(k, C[k])
    for k in sorted(W, key=str):
        print(k, W[k])
    print('time %.0f s' % (time.time() - t0))
