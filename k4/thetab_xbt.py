#!/usr/bin/env python3
"""Converse of PR #84's Proposition S1 on data (workstream proof/k4-thetab; k4/thetab.md §7, target (a)). EVIDENCE
tooling.

Statement tested, (S1c): at a Z′-maximum Q of a non-completable f = 1 key κ = (g, x) (k4/sx.md §2) with two or more
terminals, x is not big-top on g. (PR #84's Proposition S1: with exactly one terminal, x is big-top.) If (S1c) holds,
the exception (E) of Lemma P (k4/thetab.md §7) is impossible at every n, since (E) needs x big-top.

For every Z′-maximum (maximum of (r′, Λ′) over the configurations at κ) the tool records: n, ω, |T|, |V|, |V ∩ T|,
whether x is big-top on g (four goods, v_x(g) > v_x(p) + v_x(q)), and, when x is big-top with |T| >= 2, the smallest
such maximum (by n, m), with the facts used in k4/thetab.md §7: U_x ⊆ L, which leaves contain U_x.
usage: python3 k4/thetab_xbt.py DUMP.jsonl.gz ... [--every=E] [--start=S] [--max=N]   (PR #80's dumps, results/k4_sx/)"""
import collections, gzip, json, os, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, 'suite'))
from model import bits, pc                                       # noqa: E402


def x_bigtop(I, x, g):
    vs = sorted(I.v[x].values(), reverse=True)
    return len(vs) == 4 and I.v[x][g] == vs[0] and vs[0] > vs[1] + vs[2]


def analyse(kp, k, cnt, ex, src):
    I = kp.I
    x = next(i for i in range(I.n) if k[i] is not None); g = k[x]; gm = 1 << g
    free = [i for i in range(I.n) if i != x]
    U = {y: I.R[y] & ~gm for y in range(I.n)}
    cs = I.configs([k])
    lev = lambda c: sum(I.level(y, c.Q[y] & I.R[y]) for y in free)
    rob = lambda c: sum(1 for y in free if c.robust(y))
    best = max((rob(c), lev(c)) for c in cs)
    xbt = x_bigtop(I, x, g)
    keyrow = set()
    for c in cs:
        if (rob(c), lev(c)) != best: continue
        Bs = tuple(gm if i == x else (c.Q[i] & U[i]) for i in range(I.n))
        P = kp.PA[Bs]
        X = {o: c.Q[o] | c.L for o in free}
        V = [o for o in free if not any(I.threat(y, X[o], c.hv(y)) for y in free if y != o)]
        T = [z for z in free if P.N[z] & gm]
        nT = len(T) if len(T) < 3 else 3
        cnt['maxima | |T|=%s | x big-top=%s' % (nT if nT < 3 else '>=3', xbt)] += 1
        keyrow.add((min(len(T), 2), xbt))
        if len(T) >= 2 and xbt:
            cnt['S1c FAILS: maxima with |T| >= 2 and x big-top | n=%d' % I.n] += 1
            cand = (I.n, I.m, src, kp.d, list(k), repr(c), 'V', V, 'T', T,
                    'U_x in L', not (U[x] & ~c.L), 'leaves containing U_x', [o for o in V if not (U[x] & ~X[o])])
            kk = ('S1c', len(T))
            if kk not in ex or cand[:2] < ex[kk][:2]: ex[kk] = cand
        if len(T) == 1 and not xbt:
            cnt['S1 FAILS (PR #84): one terminal and x not big-top'] += 1
    for t, b in keyrow:
        cnt['keys with a maximum with |T| %s, x big-top=%s' % ('>= 2' if t == 2 else '= %d' % t, b)] += 1


def main(argv):
    print('# command: python3 k4/thetab_xbt.py ' + ' '.join(argv), flush=True)
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    rest = [a for a in argv if not a.startswith('--')]
    try:
        import sx_zprime as Z                                    # PR #80's, on main
    except ImportError:                                          # before PR #80 is merged: a local copy, if any
        sys.path.append(os.path.join(HERE, 'suite', '.cache', 'sx', 'k4'))
        import sx_zprime as Z
    profs = []
    for fn in rest:
        for line in gzip.open(fn, 'rt'):
            r = json.loads(line)
            if r.get('f', 1) == 1: profs.append(({'sets': r['sets'], 'vals': r['vals'], 'm': r['m']}, r.get('src', fn)))
    profs = profs[int(opt.get('start', 0))::int(opt.get('every', 1))]
    if 'max' in opt: profs = profs[:int(opt['max'])]
    cnt = collections.Counter(); ex = {}; t0 = time.time()
    for d, src in profs:
        kp = Z.KeyProfile(d)
        if not kp.ok or kp.I.f != 1: continue
        cnt['profiles'] += 1
        for k in kp.K:
            if kp.dstar[k] <= 0: continue
            cnt['non-completable keys'] += 1
            analyse(kp, k, cnt, ex, src)
    for k in sorted(cnt): print('  %-90s %d' % (k, cnt[k]))
    print('smallest maximum with |T| >= 2 and x big-top, per |T|:')
    for k, v in sorted(ex.items(), key=str):
        print('  |T|=%d: n=%d m=%d %s %s key=%s %s %s' % (k[1], v[0], v[1], v[2], json.dumps(v[3]), v[4], v[5],
                                                         ' '.join(map(str, v[6:]))))
    print('done; time %.0f s' % (time.time() - t0), flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
