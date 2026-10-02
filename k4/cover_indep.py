#!/usr/bin/env python3
"""A second, independent implementation of the COVER / COVER⁺ lemma tests (workstream compute/k4-cover). EVIDENCE
tooling.

Written from the statements only (k4/sx.md §2, §3, §6 on proof/k4-sx, PR #80: Lemmas A, B, B′, C, C′, A⁺, B⁺; k4/f2.md
§5 on proof/k4-f2, PR #82: Lemmas C⁺, C′⁺ and Fact 3). It shares no code with k4/cover_check.py's libraries
(k4/sx_zprime.py, k4/sx_f2.py, k4/f2_cc.py, k4/suite/model.py, k4/dl2_classify.py): the pre-allocations, f, the
min-frozen states, their removal-only deficits, the keys and the move kinds (T3, T3+) are those of k4/rt4_n5_indep.py
(the PR #86 auditor's repo-free code, imported); configurations, the maxima of (r′, Λ′), threats, terminals, kinds and
every lemma hypothesis are written here.

For each key with def* > 0 and each maximum Q, every lemma whose hypotheses hold is reported; for each such instance
the image state P′ is built and checked with k4/rt4_n5_indep.py: def(P′) <= 0 and P_Q -> P′ is a (T3) or (T3+) move
(T3 when the lemma says so). A violated conclusion is reported as LEMMA-FAIL (it would refute a written lemma).

Lemma C is tested with τ₁ any terminal (the statement says τ₁ need not be a leaf); k4/sx_zprime.py tests leaves only,
so the comparison counts that difference apart.

usage: python3 k4/cover_indep.py COVER_CHECK_OUT.jsonl.gz ... [--every=E] [--max=N] [--maxn=N] [--uncovered]
           compare with k4/cover_check.py (--uncovered: only the profiles with a key it finds uncovered)
       python3 k4/cover_indep.py --one '{"sets": ..., "vals": ..., "m": ...}'        one profile, every key"""
import collections, gzip, itertools, json, os, re, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import rt4_n5_indep as R

F1_LEMMAS = ('A', 'B1', "B1'", 'C', "C'")
F2_LEMMAS = ('A+', 'B+1', 'C+', "C'+")


class Prof:
    def __init__(self, sets, vals, m):
        self.ns = R.analyse(sets, vals, m)
        self.n = len(sets); self.m = self.ns['m']
        self.R = [frozenset(S) for S in sets]
        self.v = [dict(zip(S, V)) for S, V in zip(sets, vals)]
        self.f = self.ns['f']; self.omega = self.f - (2 * self.n - self.m)
        self.D = self.ns['D']; self.info = self.ns['info']; self.classify = self.ns['classify']
        self.keys = {}
        for P in self.ns['mf']:
            N, NA, J, fz = self.info(P)
            k = tuple(next(iter(P[i])) if fz[i] else None for i in range(self.n))
            self.keys.setdefault(k, []).append(P)
        self.dstar = {k: min(self.D[P] for P in Ps) for k, Ps in self.keys.items()}

    # values
    def val(self, i, S): return sum(self.v[i].get(g, 0) for g in S)

    def theta(self, i, Z):
        if not Z: return 0
        return self.val(i, Z) - min(self.v[i].get(h, 0) for h in Z)

    def threat(self, i, Z, H): return self.theta(i, Z) > self.val(i, H)

    def needs(self, i, B):
        b = self.val(i, B)
        return frozenset(g for g in self.R[i] if g not in B and self.v[i][g] > b)

    def admissible(self, i, A, U):
        if not A <= U or len(A) > 2: return False
        if not A: return not U
        a = self.val(i, A)
        return all(self.v[i][g] < a for g in U - A)

    def level(self, i, S):
        s = self.val(i, S); gs = sorted(self.R[i])
        return sum(1 for r in range(len(gs) + 1) for T in itertools.combinations(gs, r) if self.val(i, T) < s)


class Max:
    """a configuration at a key: frozen F with phi, free y with pairs Q[y], pool L"""
    def __init__(self, pf, k, Q):
        self.pf, self.k, self.Q = pf, k, Q
        n = pf.n
        self.F = [i for i in range(n) if k[i] is not None]
        self.free = [i for i in range(n) if k[i] is None]
        self.NA = frozenset(k[i] for i in self.F)
        self.U = [pf.R[i] - self.NA for i in range(n)]
        used = frozenset().union(*Q.values()) if Q else frozenset()
        self.L = frozenset(range(pf.m)) - self.NA - used
        self.H = [frozenset([k[i]]) if k[i] is not None else Q[i] & self.U[i] for i in range(n)]
        self.X = {o: Q[o] | self.L for o in self.free}
        self.P = tuple(self.H)                             # P_Q
        assert self.P in pf.D, ('P_Q is not a min-frozen state', self.P)
        self.J = frozenset(range(pf.m)) - frozenset().union(*self.H)
        self.N = [pf.needs(i, self.H[i]) for i in range(n)]

    def thr(self, w, Z, hold=None): return self.pf.threat(w, Z, self.H[w] if hold is None else hold)

    def robust(self, y): return self.pf.val(y, self.Q[y]) >= self.pf.val(y, self.U[y] - self.Q[y])

    def leaves(self):
        return [o for o in self.free if not any(self.thr(y, self.X[o]) for y in self.free if y != o)]

    def pairs_for_x(self, x, Z):
        return [frozenset(p) for p in itertools.combinations(sorted(Z), 2)
                if self.pf.admissible(x, frozenset(p) & self.U[x], self.U[x])]

    def kindR_s_in_L(self, o):
        """o of kind (R) (|U_o| = 4, not robust, H_o two goods without o's top a of U_o) with its fourth good in L"""
        pf = self.pf; U = self.U[o]
        if len(U) != 4 or self.robust(o): return False
        a = max(U, key=lambda g: pf.v[o][g])
        H = self.H[o]
        if a in H or len(H) != 2: return False
        s = next(iter(U - H - {a}))
        return s in self.L


def configs(pf, k):
    n = pf.n
    F = [i for i in range(n) if k[i] is not None]; NA = frozenset(k[i] for i in F)
    free = [i for i in range(n) if k[i] is None]
    Mp = sorted(set(range(pf.m)) - NA)
    U = {y: pf.R[y] - NA for y in free}
    cand = {y: [frozenset(p) for p in itertools.combinations(Mp, 2) if pf.admissible(y, frozenset(p) & U[y], U[y])]
            for y in free}
    out = []
    def rec(j, used, Q):
        if j == len(free): out.append(dict(Q)); return
        y = free[j]
        for p in cand[y]:
            if p & used: continue
            Q[y] = p; rec(j + 1, used | p, Q)
        Q.pop(y, None)
    rec(0, frozenset(), {})
    return out


def maxima(pf, k):
    cs = configs(pf, k)
    def pot(Q):
        r = sum(1 for y, q in Q.items() if pf.val(y, q) >= pf.val(y, (pf.R[y] - frozenset(g for g in k if g is not None)) - q))
        lam = sum(pf.level(y, q & pf.R[y]) for y, q in Q.items())
        return (r, lam)
    best = max(pot(Q) for Q in cs)
    return [Max(pf, k, Q) for Q in cs if pot(Q) == best]


# ---------------------------------------------------------------------------- verification of a claimed repair
class Fail(Exception):
    pass


def image(mx, changes):
    P2 = list(mx.P)
    for i, B in changes.items(): P2[i] = frozenset(B)
    return tuple(P2)


def verify(mx, P2, kinds, tag, fails):
    """def(P2) <= 0 and P_Q -> P2 is a move of one of the kinds"""
    pf = mx.pf
    if P2 not in pf.D:
        fails.append((tag, 'image not min-frozen', R.show(P2))); return False
    ks, _ = pf.classify(mx.P, P2)
    if pf.D[P2] > 0 or not (ks & set(kinds)):
        fails.append((tag, 'def(P\')=%s kinds=%s' % (pf.D[P2], sorted(ks)), R.show(P2))); return False
    return True


# ---------------------------------------------------------------------------- f = 1 (k4/sx.md §3)
def f1_lemmas(mx, fails):
    pf = mx.pf; x = mx.F[0]; g = mx.k[x]; om = pf.omega
    out = set()
    T = [z for z in mx.free if g in pf.R[z] and pf.val(z, mx.Q[z]) < pf.v[z][g]]
    V = mx.leaves()

    def bigtop(o):
        if len(pf.R[o]) != 4 or g not in pf.R[o]: return False
        us = sorted((pf.v[o][h] for h in mx.U[o]), reverse=True)
        return pf.v[o][g] > us[0] + us[1]

    def thetab(o): return om >= 2 and bigtop(o) and mx.U[o] <= mx.X[o]
    # Lemma A: o a terminal, threatening no free agent and threatening x, not θ-b(o)
    for o in T:
        if o in V and mx.thr(x, mx.X[o]) and not thetab(o):
            for Px in mx.pairs_for_x(x, mx.X[o]):
                if verify(mx, image(mx, {o: {g}, x: Px & mx.U[x]}), ('T3',), 'A', fails): out.add('A')
    # Lemma B / B′ with k = 1: τ terminal, τ -> o, o a leaf threatening x
    for tau in T:
        for o in mx.free:
            if o == tau or o not in V or not mx.thr(o, mx.X[tau]) or not mx.thr(x, mx.X[o]): continue
            if not mx.kindR_s_in_L(o):
                for Px in mx.pairs_for_x(x, mx.X[o]):
                    P2 = image(mx, {tau: {g}, o: mx.Q[tau] & mx.U[o], x: Px & mx.U[x]})
                    if verify(mx, P2, ('T3',), 'B1', fails): out.add('B1')
            else:
                U = mx.U[o]; a = max(U, key=lambda h: pf.v[o][h]); s = next(iter(U - mx.H[o] - {a}))
                if a not in mx.Q[tau]: continue
                y = next(iter(mx.Q[tau] - {a}))
                X2 = (mx.X[o] - {s}) | {y}
                for Px in mx.pairs_for_x(x, X2):
                    hold = {w: mx.H[w] for w in range(pf.n)}; hold[tau] = frozenset([g])
                    if any(pf.threat(w, X2, hold[w]) for w in range(pf.n) if w not in (x, o)): continue   # (H_B′)
                    P2 = image(mx, {tau: {g}, o: frozenset([a, s]), x: Px & mx.U[x]})
                    if verify(mx, P2, ('T3',), "B1'", fails): out.add("B1'")
    # Lemma C: τ₁ a θ-b terminal (any), o ≠ τ₁ a leaf, P_x ⊆ X_τ₁ a robust pair for x meeting U_τ₁, (H)
    for t1 in T:
        if not thetab(t1): continue
        for o in V:
            if o == t1: continue
            for Px in mx.pairs_for_x(x, mx.X[t1]):
                if pf.val(x, Px) < pf.val(x, mx.U[x] - Px) or not Px & mx.U[t1]: continue
                Y = mx.Q[o] | (mx.X[t1] - Px)
                if any(mx.thr(y, Y) for y in mx.free if y not in (o, t1)): continue                     # (H)
                if verify(mx, image(mx, {t1: {g}, x: Px & mx.U[x]}), ('T3',), 'C', fails):
                    out.add('C'); out.add('C (tau1 a leaf)' if t1 in V else 'C (tau1 not a leaf)')
    # Lemma C′: terminals exactly τ₁ ≠ τ₂, θ-b(τ₁), τ₂ threatening no free agent
    if len(T) == 2:
        for t1, t2 in (T, T[::-1]):
            if not thetab(t1) or t2 not in V: continue
            for Px in mx.pairs_for_x(x, mx.X[t1]):
                if pf.val(x, Px) < pf.val(x, mx.U[x] - Px) or pf.val(x, Px) <= pf.v[x][g]: continue
                for w in mx.U[t1] - Px:
                    Y = (mx.X[t2] | mx.Q[t1]) - Px - {w}
                    if not mx.U[t2] <= Y: continue
                    if any(mx.thr(y, Y) for y in mx.free if y not in (t1, t2)): continue                 # (H′)
                    if verify(mx, image(mx, {t1: {g}, x: Px & mx.U[x]}), ('T3',), "C'", fails): out.add("C'")
    return out


# ---------------------------------------------------------------------------- f >= 2 (k4/sx.md §6, k4/f2.md §5)
def need_chains(mx, x, end_ok):
    """need chains x = w_0, w_1, ..., w_j of distinct frozen agents (w_i needs phi(w_{i-1})) whose last good end_ok
    accepts"""
    pf = mx.pf; out = []
    def rec(ch):
        w = ch[-1]
        if end_ok(mx.k[w]): out.append(list(ch))
        for v in mx.F:
            if v not in ch and mx.k[w] in mx.N[v]: rec(ch + [v])
    rec([x])
    return out


def need_paths(mx, x):
    """need paths [τ, a_k, ..., a_1, x]: τ free needing phi(a_k), a_i frozen needing phi(a_{i-1}), a_0 = x"""
    out = []
    def rec(path):
        head = path[0]
        for i in range(mx.pf.n):
            if i in path or mx.k[head] not in mx.N[i]: continue
            if i in mx.F: rec([i] + path)
            else: out.append([i] + path)
    rec([x])
    return out


def chain_changes(mx, ch, z):
    """w_i takes phi(w_{i-1}) (i >= 1), z takes phi(w_j)"""
    c = {ch[i]: frozenset([mx.k[ch[i - 1]]]) for i in range(1, len(ch))}
    c[z] = frozenset([mx.k[ch[-1]]])
    return c


def f2_lemmas(mx, fails):
    pf = mx.pf; out = set(); om = pf.omega
    V = mx.leaves()
    # Lemma A⁺
    for o in V:
        thrF = [w for w in mx.F if mx.thr(w, mx.X[o])]
        if len(thrF) != 1: continue
        x = thrF[0]
        for ch in need_chains(mx, x, lambda gl, o=o: gl in mx.N[o]):
            if pf.theta(o, mx.X[o]) > pf.v[o][mx.k[ch[-1]]]: continue
            for Px in mx.pairs_for_x(x, mx.X[o]):
                c = chain_changes(mx, ch, o); c[x] = Px & mx.U[x]
                if verify(mx, image(mx, c), ('T3+',) if len(ch) > 1 else ('T3',), 'A+', fails): out.add('A+')
    # Lemma B⁺ with a threat path of length 1: τ -> o
    for o in V:
        thrF = [w for w in mx.F if mx.thr(w, mx.X[o])]
        if len(thrF) != 1 or mx.kindR_s_in_L(o): continue
        x = thrF[0]
        for tau in mx.free:
            if tau == o or not mx.thr(o, mx.X[tau]): continue
            for ch in need_chains(mx, x, lambda gl, tau=tau: gl in mx.N[tau]):
                for Px in mx.pairs_for_x(x, mx.X[o]):
                    c = chain_changes(mx, ch, tau); c[o] = mx.Q[tau] & mx.U[o]; c[x] = Px & mx.U[x]
                    if verify(mx, image(mx, c), ('T3+',), 'B+1', fails): out.add('B+1')
    # Lemmas C⁺ and C′⁺ (k4/f2.md §5)
    for x in mx.F:
        for path in need_paths(mx, x):
            tau = path[0]; gk = frozenset([mx.k[path[1]]]); onpath = set(path)
            G = mx.J | mx.H[tau]
            As = [frozenset(A) for r in (1, 2) for A in itertools.combinations(sorted(G & pf.R[x]), r)
                  if pf.admissible(x, frozenset(A), mx.U[x])]
            kinds = ('T3',) if len(path) == 2 else ('T3+',)
            for A in As:
                c = {path[j]: frozenset([mx.k[path[j + 1]]]) for j in range(len(path) - 1)}; c[x] = A
                P2 = image(mx, c)
                Jn = G - A
                # C⁺: o free off the path, P_x ⊆ X_τ with P_x ∩ U_x = A, Y = Q_o ∪ (X_τ \ P_x)
                for Px in itertools.combinations(sorted(mx.X[tau]), 2):
                    Px = frozenset(Px)
                    if Px & mx.U[x] != A: continue
                    for o in mx.free:
                        if o in onpath: continue
                        Y = mx.Q[o] | (mx.X[tau] - Px)
                        if pf.theta(x, Y) > pf.val(x, A): continue                                   # (a)
                        if pf.theta(tau, Y) > pf.val(tau, gk): continue                              # (b)
                        if any(mx.thr(w, Y) for w in range(pf.n) if w not in (o, tau, x)): continue  # (c)
                        if verify(mx, P2, kinds, 'C+', fails): out.add('C+')
                # C′⁺: o = x or free off the path, Y a bundle of o in P′ with |Y| = ω + 1, (a)-(c), a q of Fact 3
                hold2 = {i: (c[i] if i in c else mx.H[i]) for i in range(pf.n)}
                holder = {}
                for i in range(pf.n):
                    if len(hold2[i]) == 1 and next(iter(hold2[i])) in mx.NA: holder[next(iter(hold2[i]))] = i
                for o in [x] + [o for o in mx.free if o not in onpath]:
                    base = A if o == x else mx.H[o]
                    pool = Jn - base
                    if om + 1 < len(base): continue
                    for K in itertools.combinations(sorted(pool), om + 1 - len(base)):
                        Y = base | frozenset(K)
                        if o != x and pf.theta(x, Y) > pf.val(x, A): continue                        # (a)
                        if pf.theta(tau, Y) > pf.val(tau, gk): continue                              # (b)
                        if any(mx.thr(w, Y) for w in range(pf.n) if w not in (o, tau, x)): continue  # (c)
                        NoY = pf.needs(o, Y); NxA = pf.needs(x, A)
                        ok = False
                        for q in mx.NA:
                            if q in NoY: continue                                                    # (1)
                            if any(q in mx.N[i] for i in range(pf.n) if i not in (o, holder[q])): continue   # (2)
                            if o != x and q in NxA: continue                                         # (3)
                            ok = True; break
                        if ok and verify(mx, P2, kinds, "C'+", fails): out.add("C'+")
    return out


# ---------------------------------------------------------------------------- driver
def qstr(mx):
    return '{%s}, L=%s' % (', '.join('%d: %s' % (y, sorted(mx.Q[y])) for y in mx.free), sorted(mx.L))


def analyse(d):
    """{key: {qstr: lemmas}} for the keys with def* > 0, and the lemma failures"""
    pf = Prof(d['sets'], d['vals'], d['m'])
    res = {}; fails = []
    if pf.omega < 1 or pf.f < 1: return pf, res, fails
    for k, ds in pf.dstar.items():
        if ds <= 0: continue
        res[k] = {}
        for mx in maxima(pf, k):
            f = []
            lem = f1_lemmas(mx, f) if pf.f == 1 else f2_lemmas(mx, f)
            res[k][qstr(mx)] = lem
            fails += [(list(k), qstr(mx)) + t for t in f]
    return pf, res, fails


def main(argv):
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    rest = [a for a in argv if not a.startswith('--')]
    if '--one' in argv:
        d = json.loads(rest[0]); d.setdefault('m', 1 + max(map(max, d['sets'])))
        pf, res, fails = analyse(d)
        print('f=%d omega=%d keys=%d with def*>0: %d' % (pf.f, pf.omega, len(pf.dstar), len(res)))
        for k, mxs in res.items():
            print('key', list(k), 'def*', pf.dstar[k])
            for q, lem in mxs.items(): print('   ', q, sorted(lem))
        for f in fails: print('LEMMA-FAIL', f)
        return
    every = int(opt.get('every', 1)); mx_n = int(opt.get('max', 10 ** 9))
    print('# command: python3 k4/cover_indep.py ' + ' '.join(argv), flush=True)
    cnt = collections.Counter(); t0 = time.time(); shown = 0
    recs = []
    for fn in rest:
        for line in gzip.open(fn, 'rt'):
            try: recs.append(json.loads(line))
            except ValueError: break
    recs = [r for r in recs if r.get('keys')]
    if '--uncovered' in argv: recs = [r for r in recs if any(not kr['covered'] for kr in r['keys'])]
    if 'maxn' in opt: recs = [r for r in recs if len(r['sets']) <= int(opt['maxn'])]
    recs = recs[::every][:mx_n]
    for r in recs:
        d = {'sets': r['sets'], 'vals': r['vals'], 'm': r['m']}
        pf, res, fails = analyse(d)
        cnt['profiles'] += 1
        target = F1_LEMMAS if pf.f == 1 else F2_LEMMAS
        mine = {tuple(kr['key']): kr for kr in r['keys']}
        if set(mine) != set(res):
            cnt['MISMATCH keys with def*>0'] += 1; print('MISMATCH keys', r['sets'], r['vals'], sorted(mine), sorted(res)); continue
        for f in fails: cnt['LEMMA-FAIL'] += 1; print('LEMMA-FAIL', d, f, flush=True)
        for k, kr in mine.items():
            cnt['keys f=%d' % pf.f] += 1
            if kr['dstar'] != pf.dstar[k]: cnt['MISMATCH def*'] += 1
            theirs = {mr['Q']: set(l for l in mr['lemmas'] if l in target) for mr in kr['maxima']}
            ours = {q: set(l) & set(target) for q, l in res[k].items()}
            if set(theirs) != set(ours):
                cnt['MISMATCH maxima'] += 1; print('MISMATCH maxima', d, list(k), sorted(theirs), sorted(ours)); continue
            for q in ours:
                for l in target:
                    a, b = l in theirs[q], l in ours[q]
                    if a == b: cnt['maxima agree on %s=%s' % (l, a)] += 1
                    else:
                        tag = 'DIFF %s: cover_check %s, indep %s' % (l, a, b)
                        cnt[tag] += 1
                        if shown < 30: shown += 1; print(tag, d, list(k), q, flush=True)
            kc = bool(set().union(*theirs.values()) if theirs else False)
            ki = bool(set().union(*ours.values()) if ours else False)
            cnt['keys covered: cover_check %s, indep %s' % (kc, ki)] += 1
    for k in sorted(cnt): print('%-60s %d' % (k, cnt[k]))
    print('# time %.1f s' % (time.time() - t0))


if __name__ == '__main__':
    main(sys.argv[1:])
