#!/usr/bin/env python3
"""Referee check of k3-oc1's Lemma RF-A1* and Lemma NA (k4/k3_oc1.md §13.5 on claude/k4-k3-oc1 at 17777f1e). Own code
(k4/referee/c13_ref.py, cert_ref.py); nothing from k4/k3_oc1/, rf/, k4/oc1_hall/ or k4/sdc/ is run or imported.

  n5 EXPORT... : rebuild the n = 5 DEMOTE-0 starts (|U'| = 1, D_T' empty) from the certifier's exports (as in
      c13_ref.py build). Per start: one-absorber completion at the picks (at once / needs a move); RF path shape; the
      A1 form X (w: W = {Y_d} + J' - h, d: {g, h}, h = d's favourite good of J'); hypotheses (A1-i), (A1-ii),
      (A1-iii) (some k2), Hall's (A1-iv), (A1-iv*); X raw EFX0; the census facts. Lemma NA: its criterion against raw
      EFX0 on every injection J' -> agents, and whether a no-absorber completion exists.
  rand N SEED [K] : RF-A1* at any n on random strict instances with at most K goods per agent (default 4): every RF
      start of the lemma's setting where (A1-i)-(A1-iv*) hold must give an EFX0 X. Mutants: without (A1-iv*), without
      D_T' empty, without U' = {d}; K = 5 shows where |R_k2| <= 4 is used.
"""
import sys, gzip, json, itertools, random
from collections import Counter
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from c13_ref import val, efx0, sd, mkv, wants, receivers, threat_J, rf_path
from cert_ref import complete

def frozen(v, Y):
    U = set(receivers(v, Y))
    return [a for a in range(len(Y)) if a not in U]

def thr_bundle(v, i, S, t):
    """v_i(S) - min_S v_i > t (raw EFX0 violation of i against S; goods worth 0 included)"""
    if len(S) < 2:
        return False
    return val(v, i, S) - min(v[i][g] for g in S) > t

def a1(v, Y, Y2, u, w, d, J, J2):
    """hypotheses of RF-A1* at an RF start with path u -> w -> d; returns dict, X"""
    n = len(Y); p2 = [v[i][Y2[i]] for i in range(n)]
    g = Y2[d]; Rd = [x for x in J2 if v[d][x] > 0]
    h = max(Rd, key=lambda x: (v[d][x], -x)) if Rd else None
    out = {'h': h}
    if h is None:
        return out, None
    W = [Y[d]] + [x for x in J2 if x != h]
    X = [[y] for y in Y2]; X[w] = W; X[d] = [g, h]
    out['A1-i'] = (sorted(x for x in J if v[d][x] > 0) == sorted([g, h]) and v[d][g] + v[d][h] > v[d][Y[d]]
                   and [x for x in J2 if v[d][x] > 0] == [h])
    out['A1-ii'] = (sorted(x for x in W if v[u][x] > 0) == sorted([Y[d], Y[u]])
                    and v[u][Y[d]] + v[u][Y[u]] < v[u][Y[w]])
    k2s = [k for k in range(n) if k != d and v[k][g] > 0 and v[k][h] > 0 and v[k][Y[d]] <= p2[k]]
    out['A1-iii'] = bool(k2s)
    Fr = frozen(v, Y2)
    best = None
    for k2 in (k2s or [None]):
        ex = {w, u, k2}
        iv = all(not v[q][Y[d]] > 0 for q in Fr if q not in ex)
        ivs = all(not thr_bundle(v, q, W, p2[q]) for q in Fr if q not in ex and v[q][Y[d]] > 0)
        cand = (iv, ivs, k2)
        if best is None or (cand[0], cand[1]) > (best[0], best[1]):
            best = cand
    out['A1-iv'], out['A1-iv*'], out['k2'] = best
    return out, X

def na_check(v, Y2, J2, c):
    n = len(Y2); p2 = [v[i][Y2[i]] for i in range(n)]; anyok = False
    for f in itertools.permutations(range(n), len(J2)):
        X = [[y] for y in Y2]
        for j, a in zip(J2, f):
            X[a].append(j)
        crit = all(not (i != a and len(X[a]) == 2 and wants(v, i, Y2[a], Y2)) or val(v, i, X[i]) >= v[i][Y2[a]]
                   for i in range(n) for a in range(n))
        raw = efx0(v, X)
        c['NA: assignments'] += 1
        if crit != raw:
            c['NA: CRITERION != RAW'] += 1
        anyok |= raw
    return anyok

def n5(exports):
    c = Counter(); seen = set()
    for f in exports:
        d0 = json.load(gzip.open(f))
        for hgr in d0['hypergraphs']:
            sets = hgr['sets']; name = '%s#%d' % (hgr['list'], hgr['idx'])
            for s in hgr['starts']:
                v = mkv(sets, s['vals']); Y = list(s['picks']); n = len(Y); m = len(v[0])
                U = receivers(v, Y); J = sorted(set(range(m)) - set(Y))
                for o in s['orders']:
                    for u in U:
                        Y2 = sd(v, [u] + [a for a in o if a != u])
                        if None in Y2:
                            continue
                        key = json.dumps([sets, s['vals'], Y2])
                        if key in seen:
                            continue
                        seen.add(key)
                        U2 = receivers(v, Y2); J2 = sorted(set(range(m)) - set(Y2))
                        DT2 = [a for a in range(n) if a not in U2 and threat_J(v, a, J2, v[a][Y2[a]])]
                        if not (len(U2) == 1 and not DT2):
                            continue
                        c['DEMOTE-0 starts'] += 1; c['|J\'| = %d' % len(J2)] += 1
                        B = [{y} for y in Y2]
                        once = complete(v, B) is not None
                        c['complete at the picks (one absorber)' if once else 'need a move'] += 1
                        na = na_check(v, Y2, J2, c)
                        c['NA: no-absorber completion exists, %s' % ('at once' if once else 'need-a-move')] += na
                        P = rf_path(Y, Y2, u)
                        dd = U2[0]
                        shape = P is not None and len(P) == 3 and P[-1] == dd and Y2[dd] in J
                        if not shape:
                            c['other path shape'] += 1
                            continue
                        c['path u -> w -> d, d takes junk of Y'] += 1
                        w = P[1]
                        if sorted(J2) != sorted((set(J) - {Y2[dd]}) | {Y[u]}):
                            c['FAIL J\' = J - g + Y_u'] += 1
                        hy, X = a1(v, Y, Y2, u, w, dd, J, J2)
                        if X is None:
                            c['  d values no good of J\''] += 1; continue
                        ok = efx0(v, X)
                        allh = hy['A1-i'] and hy['A1-ii'] and hy['A1-iii'] and hy['A1-iv*']
                        c['  X EFX0' if ok else '  X not EFX0'] += 1
                        c['  hypotheses (A1-i)-(A1-iv*) hold' if allh else '  hypotheses fail'] += 1
                        if allh and not ok:
                            c['  VIOLATION: hypotheses hold, X not EFX0'] += 1
                        if ok and not allh:
                            c['  X EFX0 but hypotheses fail: %s' % [k for k in ('A1-i', 'A1-ii', 'A1-iii', 'A1-iv*') if not hy[k]]] += 1
                        if not ok and not allh:
                            c['  X not EFX0, failing: %s' % [k for k in ('A1-i', 'A1-ii', 'A1-iii', 'A1-iv*') if not hy[k]]] += 1
                        if allh:
                            c['  ... with Hall\'s (A1-iv)' if hy['A1-iv'] else '  ... only with (A1-iv*)'] += 1
                            Y0 = Y; DT0 = [a for a in frozen(v, Y0) if threat_J(v, a, J, v[a][Y0[a]])]
                            c['  ... |D_T(Y)| = %d' % len(DT0)] += 1
                            c['  ... d truly dangerous at Y: %s' % (dd in DT0)] += 1
                            if not hy['A1-iv']:
                                ex = {w, u, hy['k2']}
                                qs = [q for q in frozen(v, Y2) if q not in ex and v[q][Y[dd]] > 0]
                                for q in qs:
                                    top = max(v[q]) == v[q][Y2[q]]
                                    vj = sum(1 for x in J if v[q][x] > 0)
                                    c['  ... (A1-iv) fails on %s: q holds its top %s, values Y_u %s, junk of Y valued %d' % (
                                        name, top, v[q][Y[u]] > 0, vj)] += 1
    for k in sorted(c):
        print('  %-90s %d' % (k, c[k]))

def rand_inst(rng, n, m, K):
    while True:
        v = [[0] * m for _ in range(n)]
        for i in range(n):
            R = rng.sample(range(m), rng.randint(max(2, K - 1), K))
            while True:  # strict: distinct subset sums
                vals = [rng.randint(1, 30) for _ in R]
                sums = [sum(c) for r in range(1, len(vals) + 1) for c in itertools.combinations(vals, r)]
                if len(set(sums)) == len(sums):
                    break
            for g, a in zip(R, vals):
                v[i][g] = a
        if all(any(v[i][g] for i in range(n)) for g in range(m)):
            return v

def rand(N, seed, K):
    rng = random.Random(seed); c = Counter(); ex = {}
    for t in range(N):
        n = rng.randint(3, 5); m = n + rng.randint(2, 4)
        v = rand_inst(rng, n, m, K)
        seenY = set()
        for o in itertools.permutations(range(n)):
          o = list(o)
          Y = sd(v, o)
          if None in Y:
              continue
          J = sorted(set(range(m)) - set(Y))
          for u in receivers(v, Y):
              Y2 = sd(v, [u] + [a for a in o if a != u])
              if None in Y2 or tuple(Y2) in seenY:
                  continue
              seenY.add(tuple(Y2))
              P = rf_path(Y, Y2, u)
              if P is None or len(P) != 3 or Y2[P[-1]] not in J:
                  continue
              w, d = P[1], P[2]
              J2 = sorted(set(range(m)) - set(Y2))
              U2 = receivers(v, Y2)
              DT2 = [a for a in range(n) if a not in U2 and threat_J(v, a, J2, v[a][Y2[a]])]
              hy, X = a1(v, Y, Y2, u, w, d, J, J2)
              if X is None:
                  continue
              core = hy['A1-i'] and hy['A1-ii'] and hy['A1-iii']
              if not core:
                  continue
              ok = efx0(v, X)
              setting = (U2 == [d]) and not DT2
              for name, cond in (('full', setting and hy['A1-iv*']), ('no (A1-iv*)', setting),
                                 ('no D_T\'=0', U2 == [d] and hy['A1-iv*']), ('no U\'={d}', d in U2 and not DT2 and hy['A1-iv*'])):
                  if cond:
                      c['%s: cases' % name] += 1
                      if not ok:
                          c['%s: NOT EFX0' % name] += 1
                          if name not in ex or n < len(ex[name]['v']):
                              ex[name] = dict(v=v, order=o, u=u, w=w, d=d)
    print('  K = %d (max goods per agent)' % K)
    for k in sorted(c):
        print('  %-40s %d' % (k, c[k]))
    for k in sorted(ex):
        print('  smallest failure', k, json.dumps(ex[k]))

def gen(N, seed, K):
    """RF-A1*'s claim in Y'-terms only (the proof uses nothing else): Y' perfect SD picks, U' = {d}, D_T' empty,
    w != d, h the only good of J' that d values, W = {Y'_w} + J' - h, X: w gets W, d gets {Y'_d, h}.
    (i') v_d(Y'_d) + v_d(h) > v_d(Y'_w); (ii') some u not in {w, d} has W & R_u = {Y'_w, y} (y in J') with
    v_u(Y'_w) + v_u(y) < p'_u; (iii') some k2 != d values Y'_d and h with v_k2(Y'_w) <= p'_k2; (iv*') every frozen q
    outside {w, u, k2} valuing Y'_w has v_q(W) - min_W v_q <= p'_q. Claim: X is EFX0 when |R_i| <= 4."""
    rng = random.Random(seed); c = Counter(); ex = {}
    for t in range(N):
        n = rng.randint(3, 5); m = n + rng.randint(2, 4)
        v = rand_inst(rng, n, m, K)
        seen = set()
        for o in itertools.permutations(range(n)):
            Y2 = sd(v, list(o))
            if None in Y2 or tuple(Y2) in seen:
                continue
            seen.add(tuple(Y2))
            J2 = sorted(set(range(m)) - set(Y2)); p2 = [v[i][Y2[i]] for i in range(n)]
            U2 = receivers(v, Y2); Fr = [a for a in range(n) if a not in U2]
            DT2 = [a for a in Fr if threat_J(v, a, J2, p2[a])]
            for d in U2:
                Rd = [x for x in J2 if v[d][x] > 0]
                if len(Rd) != 1:
                    continue
                h = Rd[0]
                for w in range(n):
                    if w == d or not v[d][Y2[w]] > 0:
                        continue
                    W = [Y2[w]] + [x for x in J2 if x != h]
                    if not v[d][Y2[d]] + v[d][h] > v[d][Y2[w]]:
                        continue
                    X = [[y] for y in Y2]; X[w] = W; X[d] = [Y2[d], h]
                    ok = efx0(v, X)
                    us = [a for a in range(n) if a not in (w, d) and
                          len([x for x in W if v[a][x] > 0]) == 2 and v[a][Y2[w]] > 0 and val(v, a, W) < p2[a]]
                    k2s = [a for a in range(n) if a != d and v[a][Y2[d]] > 0 and v[a][h] > 0 and v[a][Y2[w]] <= p2[a]]
                    if not us or not k2s:
                        continue
                    hold = False; hold_nok = False
                    for u in us:
                        for k2 in k2s:
                            if all(not thr_bundle(v, q, W, p2[q]) for q in Fr
                                   if q not in (w, u, k2) and v[q][Y2[w]] > 0):
                                hold = True
                    base = (U2 == [d]) and not DT2
                    for name, cond in (('full', base and hold), ('no (iv*)', base), ('no D_T\'=0', U2 == [d] and hold),
                                       ('no U\'={d}', not DT2 and hold)):
                        if cond:
                            c['%s: cases' % name] += 1
                            if not ok:
                                c['%s: NOT EFX0' % name] += 1
                                if name not in ex or n < len(ex[name]['v']):
                                    ex[name] = dict(v=v, Y2=Y2, w=w, d=d, h=h)
                                if name == 'full':
                                    for i in range(n):
                                        if i != w and thr_bundle(v, i, W, val(v, i, X[i])):
                                            c['  full failure: violator of X_w is a k2 candidate %s, |R_i| = %d, '
                                              'values %d goods of W' % (i in k2s, sum(1 for g in range(m) if v[i][g] > 0),
                                                                        sum(1 for g in W if v[i][g] > 0))] += 1
                                        if i != d and thr_bundle(v, i, X[d], val(v, i, X[i])):
                                            c['  full failure: violator of X_d'] += 1
    print('  K = %d (max goods per agent)' % K)
    for k in sorted(c):
        print('  %-40s %d' % (k, c[k]))
    for k in sorted(ex):
        print('  smallest failure', k, json.dumps(ex[k]))

if __name__ == '__main__':
    print('$ python3 k4/referee/rfa1s_ref.py', *sys.argv[1:], flush=True)
    if sys.argv[1] == 'n5':
        n5(sys.argv[2:])
    elif sys.argv[1] == 'gen':
        gen(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]) if len(sys.argv) > 4 else 4)
    else:
        rand(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]) if len(sys.argv) > 4 else 4)
