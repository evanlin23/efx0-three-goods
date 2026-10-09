#!/usr/bin/env python3
"""Exhaustive or sampled search of one n = 4 core shaped like the exception (E) of Lemma P (`k4/thetab.md` §7)
(workstream proof/k4-zmove-f1). EVIDENCE tooling.

Sets (goods: g = 0; x's lower goods p, q, r = 1, 2, 3; tau1's 4, 5; the shared gamma = 6; tau2's 7, 8; w's 9, 10):
  x = {0,1,2,3}, tau1 = {0,4,5,6}, tau2 = {0,7,8,6}, w = {9,10,1,Z} with Z = 4 (default) or 7, 5, ...
x, tau1, tau2 are big-top on g = 0 (the shape of (E)); w is any strict balanced type with (C4) on its private goods
9, 10. For every profile it decides whether the key (0, x) is an f = 1 key and non-completable, and records the
terminal counts at its Z′-maxima (Conjecture S1c) and whether (E) holds at some Z′-maximum.

usage: python3 k4/zf1_eshape.py [--sample=N --seed=S] [--sets=JSON]"""
import collections, itertools, json, random, sys, os, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zf1_lib import Prof, Key, Conf, zmax, noncompletable, sh, bits
from zf1_embed import types


def bt_vecs():
    """value vectors (v_g, v_1, v_2, v_3) with g the top and big-top, one per order type of the subset sums"""
    out = {}
    for t in types(4):
        for perm in set(itertools.permutations(t)):
            if perm[0] != max(perm): continue
            o = sorted(perm[1:], reverse=True)
            if perm[0] <= o[0] + o[1]: continue
            sums = [sum(perm[g] for g in range(4) if S >> g & 1) for S in range(1, 16)]
            key = tuple(sorted(range(15), key=lambda i: sums[i]))
            out.setdefault(key, perm)
    return list(out.values())


def any_vecs(priv=None):
    out = {}
    for t in types(4):
        for perm in set(itertools.permutations(t)):
            if priv and perm[priv[0]] + perm[priv[1]] >= sum(perm) - perm[priv[0]] - perm[priv[1]]: continue
            sums = [sum(perm[g] for g in range(4) if S >> g & 1) for S in range(1, 16)]
            key = tuple(sorted(range(15), key=lambda i: sums[i]))
            out.setdefault(key, perm)
    return list(out.values())


def is_E(pr, K, c):
    """(E) of Lemma P at the configuration c: terminals exactly two theta-b leaves, U_x ⊆ L, valued by neither"""
    if len(c.term) != 2 or any(t not in c.leaves for t in c.term): return False
    for t in c.term:
        if not (K.omega >= 2 and pr.bigtop_on(t, K.g) and (K.U[t] & ~c.X[t]) == 0): return False
    Ux = K.U[K.x]
    if Ux & ~c.L: return False
    return all(not (Ux & K.U[t]) for t in c.term)


def main(argv):
    opts = dict(a[2:].partition('=')[::2] for a in argv if a.startswith('--'))
    sets = json.loads(opts['sets']) if 'sets' in opts else [[0, 1, 2, 3], [0, 4, 5, 6], [0, 7, 8, 6], [9, 10, 1, 4]]
    m = 1 + max(g for S in sets for g in S)
    BT = bt_vecs()
    deg = [sum(g in S for S in sets) for g in range(m)]
    W = any_vecs([k for k, g in enumerate(sets[3]) if deg[g] == 1] if sum(deg[g] == 1 for g in sets[3]) == 2 else None)
    print('# command: python3 k4/zf1_eshape.py ' + ' '.join(argv))
    print('# sets', sets, 'm', m, '; big-top vectors', len(BT), '; w vectors', len(W))
    rng = random.Random(int(opts.get('seed', 1)))
    N = int(opts.get('sample', 0))
    if N:
        it = ((rng.choice(BT), rng.choice(BT), rng.choice(BT), rng.choice(W)) for _ in range(N))
    else:
        it = itertools.product(BT, BT, BT, W)
    cnt = collections.Counter(); t0 = time.time()
    for vx, v1, v2, vw in it:
        vals = [list(vx), list(v1), list(v2), list(vw)]
        pr = Prof(sets, vals, m)
        cnt['profiles'] += 1
        if pr.is_f0(): cnt['f = 0'] += 1; continue
        K = Key(pr, 0, 0)
        if not K.is_key(): cnt['(0, x) not a key'] += 1; continue
        allc, mx = zmax(K)
        if not noncompletable(allc): cnt['key completable'] += 1; continue
        cnt['key NON-completable'] += 1
        for c in mx:
            cnt['Z′-max with %d terminals' % len(c.term)] += 1
            if len(c.term) >= 2:
                cnt['S1c VIOLATION'] += 1
                print('S1c VIOLATION', json.dumps({'sets': sets, 'vals': vals, 'm': m}), {y: sh(q) for y, q in c.Q.items()})
            if is_E(pr, K, c): cnt['(E) at a Z′-max'] += 1; print('(E)', json.dumps({'sets': sets, 'vals': vals}))
    for k in sorted(cnt): print('  %-40s %d' % (k, cnt[k]))
    print('done; time %.0f s' % (time.time() - t0))


if __name__ == '__main__':
    main(sys.argv[1:])
