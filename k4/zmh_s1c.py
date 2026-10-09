#!/usr/bin/env python3
"""Proposition S1c (≥ 2 terminals ⇒ x not big-top) and stronger forms, on data (workstream proof/k4-zmove-hall).
EVIDENCE tooling, k4/zmh_lib.py's model.

At every f = 1 key κ = (g, x) (completable or not) and every Z′-maximum state P_Q of it, record: x big-top or not,
the number of terminals (free agents that need g in P_Q), def(P_Q), def*(κ). Statements tested:
  S1    (K4.ON.S)  def*(κ) > 0 and exactly one terminal ⇒ x big-top;
  S1c   (K4.TB.S1C) def*(κ) > 0 and ≥ 2 terminals ⇒ x not big-top;
  S1c+  x big-top and ≥ 2 terminals at a Z′-maximum ⇒ def(P_Q) ≤ 0 (a statement about every key).
Inputs: gzip JSON lines / JSON lists of {sets, vals, m}, or rand:CERTFILE:K:SEED (K random strict profiles of each
core of a certificate file, types as in k4/check4.py's core_domains).

usage: python3 k4/zmh_s1c.py [--every=E] [--max=N] [--show=K] INPUT ..."""
import collections, gzip, itertools, json, os, random, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zmh_lib import Prof, load_inputs, show, pc, bits

_TYPES = {}


def types(d):
    if d not in _TYPES:
        reps = {}
        for v in itertools.product(range(1, 17), repeat=d):
            sums = [sum(v[g] for g in range(d) if S >> g & 1) for S in range(1, 1 << d)]
            if len(set(sums)) < len(sums) or max(v) >= sum(v) - max(v): continue
            order = sorted(set(sums))
            reps.setdefault(tuple(order.index(s) for s in sums), v)
        _TYPES[d] = list(reps.values())
    return _TYPES[d]


def rand_profiles(spec):
    _, path, K, seed = spec.split(':')
    rng = random.Random(int(seed))
    d = json.load(gzip.open(path))
    for c in d['cores']:
        sets, m = c['sets'], c['m']
        deg = [sum(g in S for S in sets) for g in range(m)]
        for _ in range(int(K)):
            vals = []
            for S in sets:
                priv = [k for k, g in enumerate(S) if deg[g] == 1]
                while True:
                    t = list(rng.choice(types(len(S))))
                    rng.shuffle(t)
                    if len(priv) == 2 and t[priv[0]] + t[priv[1]] >= sum(t) - t[priv[0]] - t[priv[1]]: continue
                    break
                vals.append(t)
            yield {'sets': sets, 'vals': vals, 'm': m}


def bigtop(pr, x, g):
    if len(pr.sets[x]) != 4: return False
    lo = sorted((pr.v[x][h] for h in pr.sets[x] if h != g), reverse=True)
    return pr.v[x][g] > lo[0] + lo[1]


def main(argv):
    opts = {}; ins = []
    for a in argv:
        if a.startswith('--'):
            kk, _, vv = a[2:].partition('='); opts[kk] = vv
        else: ins.append(a)
    every = int(opts.get('every', 1)); mx = int(opts.get('max', 10 ** 9)); showk = int(opts.get('show', 3))
    cnt = collections.Counter(); idx = 0; shown = collections.Counter()
    for spec in ins:
        src = rand_profiles(spec) if spec.startswith('rand:') else load_inputs(spec)
        for rec in src:
            idx += 1
            if (idx - 1) % every: continue
            if cnt['profiles'] >= mx: break
            cnt['profiles'] += 1
            pr = Prof(rec['sets'], rec['vals'], rec.get('m'))
            if pr.f != 1 or pr.omega < 1: continue
            cnt['f=1 profiles'] += 1
            for key, ds in pr.dstar.items():
                x = next(i for i in range(pr.n) if key[i] is not None)
                g = key[x]; gi = next(bits(g))
                bt = bigtop(pr, x, gi)
                zs, best = pr.zmax_states(key)
                for P in zs:
                    T = [y for y in range(pr.n) if key[y] is None and pr.needs(y, P[y]) & g]
                    nt = min(len(T), 2)
                    tag = 'def*>0' if ds > 0 else 'def*<=0'
                    cnt['%s terminals=%s bigtop=%d' % (tag, '1' if nt == 1 else ('>=2' if nt == 2 else '0'), bt)] += 1
                    if ds > 0 and nt >= 2 and bt:
                        cnt['S1c FAILS'] += 1
                        print('S1c FAILS', json.dumps({'sets': pr.sets, 'vals': [[pr.v[i][h] for h in pr.sets[i]] for i in range(pr.n)], 'm': pr.m}), 'x', x, 'g', gi, 'P_Q', show(P), flush=True)
                    if ds > 0 and nt == 1 and not bt:
                        cnt['S1 FAILS'] += 1
                    if bt and nt >= 2:
                        d = pr.D[P]
                        # nearest state of the same key with def <= 0 (number of changed free bases)
                        dist = min((sum(1 for i in range(pr.n) if P2[i] != P[i]) for P2 in pr.keys[key]
                                    if pr.D[P2] <= 0), default=None)
                        cnt['bigtop, >=2 terminals: nearest def<=0 state of the key at distance %s' % dist] += 1
                        if dist == 1:
                            # which agent re-bases, and does it take a lower good of x?
                            Ux = pr.R[x] & ~g
                            for P2 in pr.keys[key]:
                                if pr.D[P2] > 0 or sum(1 for i in range(pr.n) if P2[i] != P[i]) != 1: continue
                                y = next(i for i in range(pr.n) if P2[i] != P[i])
                                cnt['  dist-1 re-base: y %s, takes a lower good of x %d, y terminal %d, y value %s' % (
                                    'leaf?', bool(P2[y] & Ux & ~P[y]), y in T,
                                    'up' if pr.val(y, P2[y]) > pr.val(y, P[y]) else 'down')] += 1
                        cnt['bigtop, >=2 terminals: def(P_Q) %s' % ('<=0' if d <= 0 else '>0')] += 1
                        if d > 0 and shown['s1c+'] < showk:
                            shown['s1c+'] += 1
                            print('S1c+ FAILS', json.dumps({'sets': pr.sets, 'vals': [[pr.v[i][h] for h in pr.sets[i]] for i in range(pr.n)], 'm': pr.m}), 'x', x, 'g', gi, 'P_Q', show(P), 'def', d, 'def*', ds, flush=True)
    for kk in sorted(cnt): print('%-55s %d' % (kk, cnt[kk]))


if __name__ == '__main__':
    main(sys.argv[1:])
