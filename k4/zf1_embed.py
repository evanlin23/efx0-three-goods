#!/usr/bin/env python3
"""Structured hunt for f = 1 keys with a big-top frozen agent at n >= 4 (workstream proof/k4-zmove-f1). EVIDENCE tooling.

PR #80's random hunts find no non-completable f = 1 key with a big-top frozen agent at n >= 4. This tool builds such
profiles by extending a profile that has one: it adds an agent w with two new private goods p, q and two goods shared
with the existing agents (so m grows by 2, n by 1, and omega = m - 2n + 1 is kept), with a random strict balanced type
satisfying the core condition (C4) p + q < s + t. Profiles with f != 1 are skipped (f = 0: some need-free
pre-allocation; f >= 2: no f = 1 key). For every f = 1 key with a big-top frozen agent it records whether the key is
completable, and at the non-completable ones the number of terminals at every Z′-maximum (Conjecture S1c, K4.TB.S1C).

usage: python3 k4/zf1_embed.py BASE.jsonl.gz ... [--trials=T] [--seed=S] [--every=E] [--max=N] [--dump=OUT.jsonl]
       [--depth=D] (D = 1 adds one agent; 2 adds two, the second to the extended profile)"""
import collections, itertools, json, random, sys, os, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zf1_lib import Prof, Key, Conf, load, f1_keys, zmax, noncompletable, sh

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


def extend(rec, rng, minomega=2):
    """add an agent w: d = 3 or 4 goods, k >= d - 2... shared (core (C3): at most d - 2 private), the rest new
    private goods; keep omega = m - 2n + 1 >= minomega"""
    sets = [list(S) for S in rec['sets']]; vals = [list(V) for V in rec['vals']]; m = rec['m']
    n = len(sets); om = m - 2 * n + 1
    shapes = [(d, k) for d in (3, 4) for k in range(2, d + 1) if k <= m and om + (d - k) - 2 >= minomega]
    if not shapes: return None
    d, k = rng.choice(shapes)
    shared = rng.sample(range(m), k)
    S = shared + list(range(m, m + d - k))
    while True:
        t = list(rng.choice(types(d))); rng.shuffle(t)
        if d - k == 2 and t[2] + t[3] >= t[0] + t[1]: continue
        break
    return {'sets': sets + [S], 'vals': vals + [t], 'm': m + d - k}


def bigtop_nc_keys(pr):
    """(key, Z′-maxima) for the non-completable f = 1 keys with a big-top frozen agent; None if f != 1"""
    if pr.is_f0(): return None
    keys = f1_keys(pr)
    if not keys: return None
    out = []
    for K in keys:
        if not pr.bigtop_on(K.x, K.g): continue
        allc, mx = zmax(K)
        out.append((K, mx if noncompletable(allc) else None))
    return out


def main(argv):
    opts = {}; ins = []
    for a in argv:
        if a.startswith('--'):
            k, _, v = a[2:].partition('='); opts[k] = v
        else: ins.append(a)
    T = int(opts.get('trials', 20)); rng = random.Random(int(opts.get('seed', 1)))
    every = int(opts.get('every', 1)); mx_ = int(opts.get('max', 10 ** 9)); depth = int(opts.get('depth', 1))
    dump = open(opts['dump'], 'w') if 'dump' in opts else None
    cnt = collections.Counter(); t0 = time.time(); idx = 0
    print('# command: python3 k4/zf1_embed.py ' + ' '.join(argv))
    for path in ins:
        for rec in load(path):
            idx += 1
            if (idx - 1) % every: continue
            if cnt['base profiles'] >= mx_: break
            pr = Prof(rec['sets'], rec['vals'], rec['m'])
            base = bigtop_nc_keys(pr)
            if not base or not any(mxs is not None for _, mxs in base): continue
            cnt['base profiles'] += 1
            for _ in range(T):
                r = rec
                for _d in range(depth):
                    r = extend(r, rng)
                    if r is None: break
                if r is None: cnt['no shape'] += 1; continue
                p2 = Prof(r['sets'], r['vals'], r['m'])
                res = bigtop_nc_keys(p2)
                if res is None: cnt['extended: f != 1'] += 1; continue
                cnt['extended: f = 1'] += 1
                for K, mxs in res:
                    if mxs is None: cnt['big-top keys, completable'] += 1; continue
                    cnt['big-top keys, NON-completable'] += 1
                    for c in mxs:
                        cnt['Z′-maxima with %s terminal(s)' % (len(c.term) if len(c.term) < 3 else '>=3')] += 1
                        if len(c.term) >= 2:
                            cnt['S1c VIOLATION'] += 1
                            print('S1c VIOLATION', json.dumps(r), 'key', K.g, K.x, {y: sh(q) for y, q in c.Q.items()})
                    if dump: dump.write(json.dumps(dict(r, g=K.g, x=K.x)) + '\n')
    for k in sorted(cnt): print('  %-50s %d' % (k, cnt[k]))
    print('done; time %.0f s' % (time.time() - t0))


if __name__ == '__main__':
    main(sys.argv[1:])
