#!/usr/bin/env python3
"""Replay of the failed candidates of workstream proof/k4-zmove-pot (k4/zmove_pot.md §6), each with two implementations:
A = main's k4/sx_keygraph.KeyProfile on k4/suite/model.py (deficits by Lemma H1, (T3+) moves generated per state);
B = main's repo-free k4/rt4_n5_indep.py (its own 𝒫, removal-only deficits, (T3+) test pairwise over the min-frozen states).

  pareto   attempts/k4-zmove-pot-pareto.md: "zm at every Pareto-maximal (or every locally optimal) state of the key"
  trl      attempts/k4-zmove-pot-t-first.md: "zm at some (or every) maximum of (-t, r', Λ') over the key's configurations"
  ab       attempts/k4-zmove-pot-a-or-b.md: "Lemma A or Lemma B (path length 1) at some Z'-maximum, any arrangement"

zm(P): some (T3+) move from P with at most one helper reaches a min-frozen state of deficit <= 0.
usage: python3 attempts/k4_zmove_pot_attempts.py [pareto|trl|ab ...]   (all by default; log: results/k4_zmove_pot/attempts.log)"""
import itertools, json, os, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, 'k4')); sys.path.insert(0, os.path.join(ROOT, 'k4', 'suite'))
import model as M
from model import bits, pc, mask
from sx_keygraph import KeyProfile
import rt4_n5_indep as R

# core 4515 of compute/k4-rc: the first of its 42 profiles (of 1,076) with a Pareto-maximal, locally optimal stuck state
# (results/k4_zmove_pot/run_rc.log, line EX PARETO)
C4515 = {'sets': [[0, 2, 4, 8], [1, 8, 10, 11], [3, 9, 10, 11], [4, 5, 6, 7], [5, 6, 7, 9]],
         'vals': [[4, 3, 8, 2], [8, 3, 6, 10], [2, 8, 3, 4], [8, 2, 3, 4], [3, 2, 4, 8]], 'm': 12}
# core 4604 of compute/k4-rc: the first of its 369 profiles (run_rc.log, line EX TRL; all 369 keys fail the same way)
C4604 = {'sets': [[0, 2, 9, 11], [1, 6, 10, 12], [3, 7, 11, 12], [4, 8, 11, 12], [5, 9, 10, 12]],
         'vals': [[3, 5, 6, 7], [6, 5, 4, 8], [2, 3, 8, 4], [3, 2, 8, 4], [7, 6, 2, 10]], 'm': 13}
# n = 3, m = 7: both terminals are theta-b leaves (k4/sx.md §3), no slot
N3M7 = {'sets': [[0, 2, 5, 6], [1, 4, 5, 6], [3, 4, 5, 6]], 'vals': [[3, 6, 2, 10], [6, 3, 2, 10], [3, 5, 6, 7]], 'm': 7}


def lst(Bs): return [sorted(bits(B)) for B in Bs]


def zm_A(kp, Bs): return any(kp.D[b2] <= 0 for b2, x, z, W, h in kp.t3plus_moves(Bs))


def zm_B(ns, Bs):
    Pt = tuple(frozenset(bits(B)) for B in Bs)
    return any(ns['D'][Q] <= 0 and 'T3+' in ns['classify'](Pt, Q)[0] for Q in ns['mf'])


def deficits_agree(kp, ns):
    DB = {tuple(mask(B) for B in Pt): v for Pt, v in ns['D'].items()}
    assert set(DB) == set(kp.D), 'the min-frozen classes differ'
    for b, v in DB.items():
        assert (v == float('inf') and kp.D[b] >= 10 ** 9) or v == kp.D[b], ('deficit', lst(b), v, kp.D[b])


def key_data(kp, k):
    I = kp.I
    free = [y for y in range(I.n) if k[y] is None]
    Nm = mask(g for g in k if g is not None)
    U = {y: I.R[y] & ~Nm for y in range(I.n)}
    return I, free, U


def robust_count(I, free, U, b): return sum(1 for y in free if I.val(y, b[y]) >= I.val(y, U[y] & ~b[y]))


def pareto(d):
    print('== pareto: core 4515 (n = 5, m = 12, f = 2), a profile of compute/k4-rc')
    kp = KeyProfile(d); ns = R.analyse(d['sets'], d['vals'], d['m']); deficits_agree(kp, ns)
    I = kp.I
    print('f =', I.f, 'omega =', I.omega)
    found = 0
    for k in kp.K:
        if kp.dstar[k] <= 0: continue
        I, free, U = key_data(kp, k)
        sts = kp.K[k]
        vec = {b: tuple(I.val(y, b[y]) for y in free) for b in sts}
        mr = max(robust_count(I, free, U, b) for b in sts)
        for b in sts:
            P = kp.PA[b]
            par = not any(all(a >= c for a, c in zip(vec[b2], vec[b])) and vec[b2] != vec[b] for b2 in sts)
            uo = all(not any(I.val(y, mask(c)) > I.val(y, b[y]) for r in (1, 2)
                             for c in itertools.combinations(list(bits((b[y] | P.J) & I.R[y])), r)) for y in free)
            if not (par and uo): continue
            a, bb = zm_A(kp, b), zm_B(ns, b)
            assert a == bb, ('implementations disagree on zm', lst(b))
            if not a:
                found += 1
                print('key', list(k), 'def*', kp.dstar[k], 'state', lst(b), 'def', kp.D[b], 'Pareto-maximal', par,
                      'locally optimal', uo, "r' =", robust_count(I, free, U, b), "max r' =", mr, 'zm (A, B):', a, bb)
    assert found, 'no Pareto-maximal locally optimal state without zm'
    print('FAILS (%d states), both implementations' % found)


def trl(d):
    print('== trl: core 4604 (n = 5, m = 13, f = 1), a profile of compute/k4-rc')
    kp = KeyProfile(d); ns = R.analyse(d['sets'], d['vals'], d['m']); deficits_agree(kp, ns)
    I = kp.I
    print('f =', I.f, 'omega =', I.omega)
    bad = 0
    for k in kp.K:
        if kp.dstar[k] <= 0: continue
        I, free, U = key_data(kp, k)
        cs = I.configs([k])
        phi = lambda c: (-c.t, sum(1 for y in free if c.robust(y)), sum(I.level(y, c.Q[y] & I.R[y]) for y in free))
        best = max(phi(c) for c in cs)
        mx = [c for c in cs if phi(c) == best]
        states = sorted(set(tuple((1 << k[i]) if k[i] is not None else (c.Q[i] & U[i]) for i in range(I.n)) for c in mx))
        zs = []
        for b in states:
            a, bb = zm_A(kp, b), zm_B(ns, b)
            assert a == bb, ('implementations disagree on zm', lst(b))
            zs.append(a)
        z2 = max((robust_count(I, free, U, b), sum(I.level(y, b[y]) for y in free)) for b in kp.K[k])
        print('key', list(k), 'def*', kp.dstar[k], '(-t, r\', Lam\') max', best, 'maxima', len(mx), 'their states',
              [lst(b) for b in states], 'zm', zs, "| (r', Lam') max over states", z2)
        if not any(zs): bad += 1
    assert bad, 'every key has a maximum with zm'
    print('FAILS at %d key(s): no maximum of (-t, r\', Lam\') has a one-move repair; both implementations' % bad)


def ab(d):
    print('== ab: n = 3, m = 7')
    kp = KeyProfile(d); ns = R.analyse(d['sets'], d['vals'], d['m']); deficits_agree(kp, ns)
    I = kp.I
    print('f =', I.f, 'omega =', I.omega)
    hit = 0
    for k in kp.K:
        if kp.dstar[k] <= 0: continue
        I, free, U = key_data(kp, k)
        x = next(i for i in range(I.n) if k[i] is not None); g = k[x]; gm = 1 << g
        cs = I.configs([k])
        phi = lambda c: (sum(1 for y in free if c.robust(y)), sum(I.level(y, c.Q[y] & I.R[y]) for y in free))
        best = max(phi(c) for c in cs)
        for c in cs:
            if phi(c) != best: continue
            X = {o: c.Q[o] | c.L for o in free}
            thr = lambda o, w: I.threat(w, X[o], c.hv(w))
            V = [o for o in free if not any(thr(o, y) for y in free if y != o)]
            Bs = tuple(gm if i == x else (c.Q[i] & U[i]) for i in range(I.n))
            T = [z for z in free if kp.PA[Bs].N[z] & gm]
            thb = {t: len(I.sets[t]) == 4 and I.v[t][g] > sum(sorted((I.v[t][h] for h in bits(U[t])), reverse=True)[:2])
                   and not (U[t] & ~X[t]) and I.omega >= 2 for t in T}
            A_applies = any(t in V and not thb[t] for t in T)
            B1_applies = any(t not in V and any(thr(t, o) for o in V) for t in T)
            a, bb = zm_A(kp, Bs), zm_B(ns, Bs)
            assert a == bb
            print('key', list(k), 'Z\'-maximum', c, 'leaves', V, 'terminals', T, 'theta-b', thb,
                  'Lemma A applies', A_applies, 'Lemma B (k = 1) applies', B1_applies, 'zm (A, B):', a, bb)
            assert not A_applies and not B1_applies and a
            hit += 1
    assert hit
    print('FAILS: no Z\'-maximum (any arrangement) has Lemma A or B with path length 1; zm holds (Lemmas C, C\')')


if __name__ == '__main__':
    which = sys.argv[1:] or ['pareto', 'trl', 'ab']
    for w in which:
        {'pareto': lambda: pareto(C4515), 'trl': lambda: trl(C4604), 'ab': lambda: ab(N3M7)}[w]()
    print('ALL CONFIRMED')
