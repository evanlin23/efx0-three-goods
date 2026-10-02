#!/usr/bin/env python3
"""The single-terminal regime at Theorem Z′'s configuration (workstream proof/k4-oneneeder; k4/oneneeder.md §5).
EVIDENCE tooling, on k4/suite/model.py only.

For every profile with f = 1 and omega >= 1, every key κ = (g, x) with no completable configuration (def*(κ) > 0, by
k4/c4min.md Lemma 1 / k4/sx.md Lemma 0), and every configuration Q at κ maximizing (r', Λ') (r' = robust free agents,
Λ' = the sum over the free agents of the levels of Q_y ∩ R_y; a "Z′-maximum", k4/sx.md §2): T = the terminals (free
agents needing g at their holding), V = the leaves (free agents whose bundle X_o = Q_o ∪ L threatens no free agent).
When |T| = 1 (the one-needer regime; T = {tau}) the tool asserts:
  S1   x is big-top on g (k4/oneneeder.md §5, Proposition S1);
checks that k4/sx.md's Lemma A (tau a leaf, not theta-b) and Lemma B (k = 1, leaf not (R) with s in the pool) reach
deficit <= -1 here (Corollary 8.2 with |Z| = omega + 2), and checks the two constructions of §5 wherever they apply, asserting their conclusion against the exact deficit
(model.Inst.deficit) of the swapped state, which must be min-frozen:
  Ab   (tau in V, theta-b(tau)): R_tau = R_x asserted (part (i)); tau takes {g}, x takes an admissible set inside
       Z := X_tau minus one good l, chosen with v_x(Z) > v_x(g) and theta_tau(Z) < v_tau(g); def(P') <= 0 asserted, and
       such an l asserted to exist when omega = 2 (part (ii));
  Bb   (tau -> o, o in V of kind (R) with its fourth good s in the pool, s not a good of x; then v_x(X_o minus s) >
       v_x(g), asserted): tau takes {g}, o takes {a_o, s}, x takes an admissible set inside X_o minus s; def(P') <= 0
       asserted.
It also records which of k4/sx.md's cases the Z′-maximum is in (regime I: tau in V, theta-b or not; regime II: path
length k, the leaf's kind, s in L).

usage: python3 k4/oneneeder_zprime.py DUMP.jsonl.gz ... [--every=E] [--max=N]   (k4/sx_hunt.py dumps: f = 1 profiles)"""
import collections, gzip, itertools, json, os, sys, time
T0 = time.time()
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'suite'))
import model as M
from model import bits, pc, mask


def bigtop_on(I, y, g):
    if len(I.sets[y]) != 4: return False
    vs = sorted(I.v[y].values(), reverse=True)
    return I.v[y].get(g) == vs[0] and vs[0] > vs[1] + vs[2]


def theta(I, y, Z):
    return I.val(y, Z) - (min(I.v[y].get(q, 0) for q in bits(Z)) if Z and not Z & ~I.R[y] else 0) if Z else 0


def adm_inside(I, x, Z, Ux):
    for k in (2, 1):
        for A in itertools.combinations(sorted(bits(Z & Ux), key=lambda q: -I.v[x][q]), k):
            if I.admissible(x, mask(A), Ux): return mask(A)
    return None


def swap_def(I, Bs):
    Bs = tuple(Bs)
    if Bs not in I._minset: return None
    return I.deficit(Bs)


def analyse(I, key, cnt, ex):
    x = next(i for i in range(I.n) if key[i] is not None); g = key[x]; gm = 1 << g
    free = [i for i in range(I.n) if i != x]
    U = {y: I.R[y] & ~gm for y in range(I.n)}
    cs = I.configs([key])
    if any(c.completable for c in cs): return
    cnt['non-completable keys'] += 1
    lev = lambda c: sum(I.level(y, c.Q[y] & I.R[y]) for y in free)
    rob = lambda c: sum(1 for y in free if c.robust(y))
    best = max((rob(c), lev(c)) for c in cs)
    for c in cs:
        if (rob(c), lev(c)) != best: continue
        cnt['Z-maxima'] += 1
        X = {o: c.Q[o] | c.L for o in free}
        T = [y for y in free if I.R[y] & gm and I.val(y, c.Q[y]) < I.v[y][g]]
        V = [o for o in free if not any(I.threat(y, X[o], c.hv(y)) for y in free if y != o)]
        if len(T) != 1:
            cnt['Z-maxima with %d terminals, x big-top=%s' % (len(T), bigtop_on(I, x, g))] += 1
            continue
        tau = T[0]
        bt = bigtop_on(I, x, g)
        cnt['single terminal: Z-maxima'] += 1
        assert bt, ('Proposition S1 violated: single terminal, x not big-top', I.sets, [[I.v[i][q] for q in I.sets[i]] for i in range(I.n)], repr(c))
        Bs0 = [gm if i == x else c.Q[i] & U[i] for i in range(I.n)]
        if tau in V:
            thb = bigtop_on(I, tau, g) and not (U[tau] & ~X[tau]) and I.omega >= 2
            cnt['single terminal: regime I (tau a leaf), theta-b=%s' % thb] += 1
            if not thb:
                # sx Lemma A in this regime is a Corollary 8.2 swap with |Z| = omega + 2: def(P') <= -1
                Bs = list(Bs0); Bs[tau] = gm; Bs[x] = adm_inside(I, x, X[tau], U[x])
                d = swap_def(I, Bs)
                assert d is not None and d <= -1, ('Lemma A image: deficit', I.sets, repr(c), d)
                cnt['single terminal: Lemma A image has def <= -1'] += 1
                continue
            # Lemma A-flat (i): a theta-b single terminal leaf is a twin of x (otherwise P_Q has def <= 0)
            assert U[tau] == U[x], ('Lemma Ab(i) violated: theta-b single terminal, not a twin', I.sets, repr(c))
            done = False
            for l in bits(X[tau]):
                Z = X[tau] & ~(1 << l)
                if I.val(x, Z) <= I.v[x][g] or theta(I, tau, Z) >= I.v[tau][g]: continue
                A = adm_inside(I, x, Z, U[x])
                Bs = list(Bs0); Bs[tau] = gm; Bs[x] = A
                d = swap_def(I, Bs)
                assert d is not None and d <= 0, ('Lemma Ab violated', I.sets, repr(c), l, d)
                done = True; break
            assert done or I.omega >= 3, ('Lemma Ab(ii) violated: omega = 2 and no swap', I.sets, repr(c))
            cnt['single terminal: theta-b leaf, Lemma Ab applies=%s omega=%d' % (done, I.omega)] += 1
            if not done and len(ex['Ab-fails']) < 3: ex['Ab-fails'].append((I.sets, [[I.v[i][q] for q in I.sets[i]] for i in range(I.n)], repr(c)))
            continue
        # regime II: every threat path from tau to a leaf (Lemma F of k4/sx.md: an out-forest)
        out = {u: [y for y in free if y != u and I.threat(y, X[u], c.hv(y))] for u in free}
        paths = []
        def walk(u, pth):
            if not out[u]: paths.append(pth); return
            for w in out[u]:
                assert w not in pth, 'a threat cycle at a Z-maximum'
                walk(w, pth + [w])
        walk(tau, [tau])
        for path in paths:
            o = path[-1]; k = len(path) - 1
            assert o in V
            kind = 'other'; sL = False
            if pc(U[o]) == 4 and not c.robust(o):
                gs = sorted(bits(U[o]), key=lambda h: -I.v[o][h])
                H = c.Q[o] & U[o]
                if not H & (1 << gs[0]) and pc(H) == 2:
                    kind = 'R'; a = gs[0]; s = next(bits(U[o] & ~H & ~(1 << a))); sL = bool(c.L >> s & 1)
            cnt['single terminal: regime II path, k=%d, leaf kind %s%s' % (k, kind, ' s in L' if sL else '')] += 1
            if k == 1 and not sL:
                # sx Lemma B (k = 1) in this regime is a Corollary 8.2 swap with helper o, |Z| = omega + 2: def(P') <= -1
                Bs = list(Bs0); Bs[tau] = gm; Bs[o] = c.Q[tau] & U[o]; Bs[x] = adm_inside(I, x, X[o], U[x])
                d = swap_def(I, Bs)
                assert d is not None and d <= -1, ('Lemma B image: deficit', I.sets, repr(c), d)
                cnt['single terminal: Lemma B (k=1) image has def <= -1'] += 1
            if k == 1 and kind == 'R' and sL:
                Z = X[o] & ~(1 << s)
                ok = I.val(x, Z) > I.v[x][g]
                cnt['single terminal: (R) leaf with s in L, k=1: v_x(X_o - s) > v_x(g) = %s (s in U_x = %s)' % (ok, bool(U[x] >> s & 1))] += 1
                assert ok == (not U[x] >> s & 1), 'Lemma Bb: v_x(X_o - s) > v_x(g) iff s is not a good of x'
                if ok:
                    A = adm_inside(I, x, Z, U[x])
                    Bs = list(Bs0); Bs[tau] = gm; Bs[x] = A; Bs[o] = ((1 << a) | (1 << s)) & U[o]
                    d = swap_def(I, Bs)
                    assert d is not None and d <= 0, ('Lemma Bb violated', I.sets, repr(c), d)
                    cnt['single terminal: Lemma Bb applies'] += 1


def main(argv):
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    files = [a for a in argv if not a.startswith('--')]
    print('# command: python3 k4/oneneeder_zprime.py ' + ' '.join(argv), flush=True)
    cnt = collections.Counter(); ex = collections.defaultdict(list)
    profs = []
    for fn in files:
        for l in gzip.open(fn, 'rt'):
            r = json.loads(l)
            if r.get('f', 1) == 1: profs.append(r)
    profs = profs[::int(opt.get('every', 1))]
    if 'max' in opt: profs = profs[:int(opt['max'])]
    for r in profs:
        I = M.Inst(r['sets'], r['vals'], r.get('m'))
        I.preallocs()
        if I.f != 1 or I.omega < 1: continue
        I._minset = set(Bs for Bs, NA in I.minP)
        cnt['profiles'] += 1
        for key in I.keys: analyse(I, key, cnt, ex)
    for k in sorted(cnt): print('%-100s %d' % (k, cnt[k]))
    for k, v in ex.items():
        for e in v: print('EX', k, e)
    print('no assertion failed [%.0f s]' % (time.time() - T0))


if __name__ == '__main__':
    main(sys.argv[1:])
