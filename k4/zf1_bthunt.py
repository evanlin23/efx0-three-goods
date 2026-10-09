#!/usr/bin/env python3
"""Hill-climbing hunt for non-completable f = 1 keys with a big-top frozen agent (workstream proof/k4-zmove-f1).
EVIDENCE tooling.

For a random core of the given certificate files (connected k = 4 cores; m - 2n + 1 >= 2) it draws a strict profile
satisfying the core condition (C4), then repeatedly redraws one agent's value type, keeping the change when the
score does not get worse. Score: over the f = 1 keys (g, x) with x big-top on g, the least number of completable
configurations (infinite if the profile has f != 1 or no such key). A key with score 0 is non-completable; it is
reported with the terminal counts at its Z′-maxima (Conjecture S1c, K4.TB.S1C) and dumped.

usage: python3 k4/zf1_bthunt.py CERTS.json.gz ... [--runs=R] [--steps=S] [--seed=K] [--dump=OUT.jsonl]"""
import collections, gzip, json, random, sys, os, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zf1_lib import Prof, Key, Conf, f1_keys, zmax, noncompletable, sh
from zf1_embed import types

INF = 10 ** 9


def draw(rng, S, deg, bt=False):
    """a random strict balanced type for the goods S with (C4); bt: big-top (top > second + third), top not private"""
    priv = [k for k, g in enumerate(S) if deg[g] == 1]
    while True:
        t = list(rng.choice(types(len(S)))); rng.shuffle(t)
        if len(priv) == 2 and t[priv[0]] + t[priv[1]] >= sum(t) - t[priv[0]] - t[priv[1]]: continue
        if bt:
            if len(S) != 4: return None
            o = sorted(t, reverse=True)
            if o[0] <= o[1] + o[2] or t.index(o[0]) in priv: continue
        return t


def score(sets, vals, m):
    pr = Prof(sets, vals, m)
    if pr.is_f0(): return INF, None
    keys = f1_keys(pr)
    best = INF; arg = None
    for K in keys:
        if not pr.bigtop_on(K.x, K.g): continue
        nc = 0
        for Q in K.configs():
            if Conf(K, Q).completable() is not None: nc += 1
        if nc < best: best = nc; arg = K
    return best, (pr, arg)


def main(argv):
    opts = {}; ins = []
    for a in argv:
        if a.startswith('--'):
            k, _, v = a[2:].partition('='); opts[k] = v
        else: ins.append(a)
    rng = random.Random(int(opts.get('seed', 1)))
    runs = int(opts.get('runs', 50)); steps = int(opts.get('steps', 200))
    dump = open(opts['dump'], 'a') if 'dump' in opts else None
    cores = []
    for p in ins:
        d = json.load(gzip.open(p))
        for c in d['cores']:
            n = len(c['sets'])
            if c['m'] - 2 * n + 1 >= 2: cores.append((p, c))
    print('# command: python3 k4/zf1_bthunt.py ' + ' '.join(argv))
    print('# cores with omega >= 2:', len(cores))
    cnt = collections.Counter(); t0 = time.time()
    for run in range(runs):
        p, c = rng.choice(cores)
        sets, m = c['sets'], c['m']
        deg = [sum(g in S for S in sets) for g in range(m)]
        four = [i for i, S in enumerate(sets) if len(S) == 4]
        if not four: continue
        xb = rng.choice(four)
        vals = [draw(rng, S, deg, bt=(i == xb)) for i, S in enumerate(sets)]
        sc, _ = score(sets, vals, m)
        for st in range(steps):
            if sc == 0: break
            i = rng.randrange(len(sets))
            nv = list(vals); nv[i] = draw(rng, sets[i], deg, bt=(i == xb))
            s2, _ = score(sets, nv, m)
            if s2 <= sc: vals, sc = nv, s2
        cnt['runs'] += 1
        cnt['final score %s' % ('inf' if sc == INF else ('0' if sc == 0 else '>0'))] += 1
        if sc == 0:
            _, (pr, K) = score(sets, vals, m)
            allc, mx = zmax(K)
            assert noncompletable(allc)
            terms = sorted(len(cf.term) for cf in mx)
            print('NC big-top key: core %s#%s sets %s vals %s m %d key (g=%d, x=%d) terminals at the Z′-maxima %s'
                  % (os.path.basename(p), c.get('idx'), sets, vals, m, K.g, K.x, terms))
            cnt['NC big-top keys'] += 1
            if any(t >= 2 for t in terms): cnt['S1c VIOLATION'] += 1; print('S1c VIOLATION')
            if dump: dump.write(json.dumps({'sets': sets, 'vals': vals, 'm': m, 'g': K.g, 'x': K.x}) + '\n'); dump.flush()
    for k in sorted(cnt): print('  %-40s %d' % (k, cnt[k]))
    print('done; time %.0f s' % (time.time() - t0))


if __name__ == '__main__':
    main(sys.argv[1:])
