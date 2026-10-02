#!/usr/bin/env python3
"""Roles in the ZMOVE repairs (workstream proof/k4-zmove-hall). EVIDENCE tooling, k4/zmh_lib.py's model.

At every Z′-maximum state P_Q of every key with def* > 0, for one configuration Q over P_Q (the first filler
assignment) it computes Lemma F⁺'s forest (threats among free agents, leaves V, the frozen agents each leaf threatens,
the free needers of each frozen good) and, for every (T3⁺) move with at most one helper from P_Q to a state P′ with
def(P′) <= 0, the roles: x (threatened by which leaves), z (leaf / internal / root; needer of φ(x) or chain end), the
helper (role; whether it takes goods of B_z), and every owner o′ that attains def(P′) <= 0 in P′ (Lemma H1) with
its role (x, z, helper, leaf, other free) and the size of its optimal bundle and u′.

usage: python3 k4/zmh_roles.py [--max=N] [--every=E] [--show=K] INPUT ..."""
import collections, json, os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zmh_lib import Prof, load_inputs, show, pc, bits


def forest(pr, key, Q, L):
    n = pr.n
    free = [y for y in range(n) if key[y] is None]
    F = [w for w in range(n) if key[w] is not None]
    hv = {y: pr.val(y, Q[y]) for y in free}
    hv.update({w: pr.val(w, key[w]) for w in F})
    X = {o: Q[o] | L for o in free}
    thr = {o: [w for w in range(n) if w != o and pr.threat(w, X[o], hv[w])] for o in free}
    V = [o for o in free if not any(w in free for w in thr[o])]
    return free, F, X, thr, V, hv


def analyse(pr, key, P, cnt, ex, showk):
    n = pr.n
    cfgs = pr.configs_over(P, key)
    Q, L = cfgs[0]
    free, F, X, thr, V, hv = forest(pr, key, Q, L)
    fz = {w for w in F}
    N = [pr.needs(i, P[i]) for i in range(n)]
    indeg = collections.Counter(w for o in free for w in thr[o] if w in free)
    role = {}
    for y in free:
        role[y] = 'leaf' if y in V else ('root' if not indeg[y] else 'int')
    # frozen agents threatened by leaves
    tl = {w: [o for o in V if w in thr[o]] for w in F}
    good = [Qp for Qp in pr.states if pr.D[Qp] <= 0]
    found = False
    pats = set()
    flags = set()
    for Qp in good:
        k, (ch, U, Z, W, Y) = pr.move_kind(P, Qp)
        if 'T3+' not in k: continue
        found = True
        x, z = U[0], Z[0]
        h = Y[0] if Y else None
        g = key[x]
        zrole = role[z] + ('/needs-phi(x)' if N[z] & g else '/chain')
        xr = 'x-thr-by-leaf' if tl[x] else 'x-not-thr-by-leaf'
        hr = '-' if h is None else role[h] + ('+takesBz' if Qp[h] & P[z] else '') + \
            ('+robust' if pr.val(h, P[h]) >= pr.val(h, (pr.R[h] & ~sum_(key)) & ~P[h]) else '')
        # owners in P′
        inf = pr.info(Qp)
        owners = []
        for o in range(n):
            if inf[3][o]: continue
            v, Z_ = pr.owner_val(Qp, o, inf)
            if pr.omega + 2 - v <= 0:
                orole = 'x' if o == x else ('h' if o == h else role.get(o, '?'))
                owners.append('%s(|Y|=%d,u=%d)' % (orole, pc(Z_), v - pc(Z_)))
        pat = (zrole, xr, 'W%d' % len(W), hr, tuple(sorted(set(o.split('(')[0] for o in owners))))
        pats.add(pat)
        cnt['move ' + repr(pat)] += 1
        for o in owners:
            orole = o.split('(')[0]
            flags.add(('owner=x' if orole == 'x' else 'owner=h' if orole == 'h' else 'owner=unmoved') +
                      (' nohelper' if h is None else ' helper') + ' W%d' % min(len(W), 1))
        flags.add('any' + (' nohelper' if h is None else ' helper') + ' W%d' % min(len(W), 1))
    # simplest pattern per maximum
    regime = 'f=%d leaves=%d terminals-leaves=%d' % (pr.f, len(V), sum(1 for o in V if any(N[o] & key[w] for w in F)))
    cnt['max ' + regime] += 1
    if not found:
        cnt['max WITHOUT move'] += 1
    for p in sorted(pats):
        cnt['max-pattern ' + repr(p)] += 1
    for fl in flags: cnt['max-flag ' + fl] += 1
    # which single restriction would still cover this maximum
    for name, test in (('only owner=x', lambda s: any(t.startswith('owner=x') for t in s)),
                       ('only nohelper', lambda s: any('nohelper' in t for t in s)),
                       ('only W0', lambda s: any(t.endswith('W0') for t in s)),
                       ('only nohelper W0', lambda s: any(t.endswith('nohelper W0') for t in s)),
                       ('only owner=x or unmoved', lambda s: any(t.startswith('owner=x') or t.startswith('owner=unmoved') for t in s)),
                       ('only owner=x/unmoved, W0', lambda s: any((t.startswith('owner=x') or t.startswith('owner=unmoved')) and t.endswith('W0') for t in s))):
        if not test(flags): cnt['max NOT covered by ' + name] += 1
    if showk and len(ex) < showk:
        ex.append((pr, key, P, Q, L, V, thr, pats))


def sum_(key):
    s = 0
    for b in key:
        if b is not None: s |= b
    return s


def main(argv):
    opts = {}; ins = []
    for a in argv:
        if a.startswith('--'):
            kk, _, vv = a[2:].partition('='); opts[kk] = vv
        else: ins.append(a)
    mx = int(opts.get('max', 10 ** 9)); every = int(opts.get('every', 1)); showk = int(opts.get('show', 0))
    cnt = collections.Counter(); ex = []; idx = 0
    for path in ins:
        for rec in load_inputs(path):
            idx += 1
            if (idx - 1) % every: continue
            if cnt['profiles'] >= mx: break
            cnt['profiles'] += 1
            pr = Prof(rec['sets'], rec['vals'], rec.get('m'))
            if pr.omega < 1: continue
            for key, ds in pr.dstar.items():
                if ds <= 0: continue
                zs, best = pr.zmax_states(key)
                for P in zs: analyse(pr, key, P, cnt, ex, showk)
    for kk in sorted(cnt): print('%7d  %s' % (cnt[kk], kk))
    for pr, key, P, Q, L, V, thr, pats in ex:
        print('---', json.dumps({'sets': pr.sets, 'vals': [[pr.v[i][g] for g in pr.sets[i]] for i in range(pr.n)], 'm': pr.m}))
        print('  key', [None if b is None else list(bits(b)) for b in key], 'P_Q', show(P), 'Q', {y: list(bits(q)) for y, q in Q.items()}, 'L', list(bits(L)))
        print('  leaves', V, 'threats', thr)
        for p in sorted(pats): print('   ', p)


if __name__ == '__main__':
    main(sys.argv[1:])
