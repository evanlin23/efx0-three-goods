#!/usr/bin/env python3
"""Referee check of twins' Lemma ABS' and Lemma CH (k4/RFMIN.md §6 on proof/k4-rf-min at 6dc5e9c1). Own code
(c13_ref.py, cert_ref.py, rfmin_ref.py); nothing from k4/rfmin/ is run.

  absp N SEED K : ABS' at general states. Random strict instances (at most K goods per agent), a random SD order, the
      picks Y, and every state B one official move away (cert_ref.moves: additions, chains, rings) plus B = Y. For every
      f with B_f = {p}, p valued by nobody else, test (A0)-(A3); where they hold, build ABS''s allocation (receivers in
      random order take their best free good if the free goods are worth more than b_r to them; f takes the rest) and
      check one-absorber and raw EFX0. Mutants: drop (A1), (A2) or (A3).
  ch N SEED     : Lemma CH at maximum-matching starts of random strict cores with a private-top agent f. For every frozen d
      valuing junk, every improving pair H0 and every wanter chain from d (all branches): every x_i holds a pick; the
      move is official; (A0), (A1), (A2), d's (A3) hold at B'; ABS' holds at B' unless (V1) or (V2); (V1) with
      q not in D^full needs v_q(Y_{x_t}) > 0; and wherever ABS''s hypotheses hold, its construction is EFX0.
"""
import sys, itertools, random, json
from collections import Counter
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from c13_ref import val, efx0, sd
from cert_ref import moves, nu
from rfmin_ref import rand_strict

def recv_state(v, B, f):
    n = len(B)
    b = [val(v, i, B[i]) for i in range(n)]
    out = []
    for r in range(n):
        if r == f or len(B[r]) > 1:
            continue
        g = next(iter(B[r]), None)
        if g is None or not any(i != r and v[i][g] > b[i] for i in range(n)):
            out.append(r)
    return out

def hyps(v, B, f, J):
    n = len(B); b = [val(v, i, B[i]) for i in range(n)]
    h = {}
    h['A0'] = len(B[f]) == 1 and not any(i != f and v[i][next(iter(B[f]))] > 0 for i in range(n))
    h['A1'] = all(v[i][g] <= b[i] for i in range(n) for g in J)
    h['A2'] = all(val(v, i, B[q]) - v[i][hh] <= b[i] for q in range(n) if q != f and len(B[q]) >= 2
                  for i in range(n) if i != q for hh in B[q])
    R = recv_state(v, B, f)
    h['A3'] = all(val(v, i, J) <= b[i] for i in range(n) if i != f and i not in R)
    return h, R

def construct(v, B, f, J, R, rng):
    n = len(B); X = [set(x) for x in B]; free = set(J); b = [val(v, i, B[i]) for i in range(n)]
    order = list(R); rng.shuffle(order)
    for r in order:
        if val(v, r, free) > b[r]:
            g = max(free, key=lambda g: (v[r][g], -g)); X[r].add(g); free.discard(g)
    X[f] |= free
    extra = [len(X[i] - B[i]) for i in range(n)]
    one = sum(1 for e in extra if e >= 2) <= 1
    return X, one

def absp(N, seed, K):
    rng = random.Random(seed); c = Counter(); ex = {}
    for t in range(N):
        n = rng.randint(3, 5); m = n + rng.randint(1, 4)
        v = rand_strict(rng, n, m, 2, K)
        o = list(range(n)); rng.shuffle(o)
        Y = sd(v, o)
        B0 = [({y} if y is not None else set()) for y in Y]
        states = [B0] + moves(v, B0, rings=True)
        for B in states:
            J = set(range(m)) - set().union(*B)
            for f in range(n):
                if len(B[f]) != 1:
                    continue
                h, R = hyps(v, B, f, J)
                if not h['A0']:
                    continue
                X, one = construct(v, B, f, J, R, rng)
                ok = one and efx0(v, [sorted(x) for x in X])
                for name, req, dropped in (('full', ('A1', 'A2', 'A3'), None), ('no (A1)', ('A2', 'A3'), 'A1'),
                                           ('no (A2)', ('A1', 'A3'), 'A2'), ('no (A3)', ('A1', 'A2'), 'A3')):
                    if all(h[q] for q in req) and (dropped is None or not h[dropped]):
                        c['%s: cases' % name] += 1
                        if not ok:
                            c['%s: NOT EFX0 / not one-absorber' % name] += 1
                            if name not in ex:
                                ex[name] = dict(v=v, B=[sorted(x) for x in B], f=f)
    print('  K = %d' % K)
    for k in sorted(c):
        print('  %-45s %d' % (k, c[k]))
    for k in sorted(ex):
        print('  first failure', k, json.dumps(ex[k]))

def core_privtop(rng, n):
    """random strict instance (3-4 goods per agent, connected, every good valued) with agent 0's top good private"""
    while True:
        m = rng.randint(n + 1, n + 5)
        v = rand_strict(rng, n, m, 3, 4)
        if not all(any(v[i][g] for i in range(n)) for g in range(m)):
            continue
        seen = {0}; st = [0]
        while st:
            i = st.pop()
            for j in range(n):
                if j not in seen and any(v[i][g] and v[j][g] for g in range(m)):
                    seen.add(j); st.append(j)
        if len(seen) != n:
            continue
        p = max(range(m), key=lambda g: v[0][g])
        if any(v[i][p] > 0 for i in range(1, n)):
            continue
        return v, p

def wants(v, Y, i, j):
    return Y[j] is not None and v[i][Y[j]] > (v[i][Y[i]] if Y[i] is not None else 0)

def chains_from(v, Y, d):
    n = len(Y)
    out = []
    def rec(path):
        last = path[-1]
        ws = [i for i in range(n) if i != last and wants(v, Y, i, last)]
        if not ws:
            if len(path) >= 2:
                out.append(list(path))
            return
        for w in ws:
            if w in path:
                out.append(None); continue   # a cycle would refute acyclicity
            rec(path + [w])
    rec([d])
    return out

def ch(N, seed):
    rng = random.Random(seed); c = Counter()
    for t in range(N):
        n = rng.randint(4, 6)
        v, p = core_privtop(rng, n); f = 0; m = len(v[0])
        N0 = nu(v); seen = set()
        for o in itertools.permutations(range(n)):
            Y = tuple(sd(v, list(o)))
            if Y in seen or sum(1 for y in Y if y is not None) != N0:
                continue
            seen.add(Y)
            J = set(range(m)) - set(y for y in Y if y is not None)
            pv = [v[i][Y[i]] if Y[i] is not None else 0 for i in range(n)]
            frozen = [a for a in range(n) if Y[a] is not None and any(i != a and wants(v, Y, i, a) for i in range(n))]
            Dfull = [a for a in frozen if val(v, a, J) > pv[a]]
            c['MM starts'] += 1
            c['f holds its private top' if Y[f] == p else 'F DOES NOT HOLD ITS TOP'] += 1
            for d in frozen:
                if not any(v[d][g] > 0 for g in J):
                    continue
                for H0 in itertools.chain(itertools.combinations(sorted(J), 2), itertools.combinations(sorted(J), 3)):
                    if not (all(v[d][g] > 0 for g in H0) and val(v, d, H0) > pv[d]):
                        continue
                    for P in chains_from(v, Y, d):
                        if P is None:
                            c['CYCLE IN WANTING'] += 1; continue
                        c['chains tried (|H0| = %d)' % len(H0)] += 1
                        if any(Y[x] is None for x in P[1:]):
                            c['  A CHAIN MEMBER IS PICKLESS'] += 1; continue
                        if f in P:
                            c['  F IN THE CHAIN'] += 1
                        B = [({y} if y is not None else set()) for y in Y]
                        B2 = [set(x) for x in B]; B2[d] = set(H0)
                        for i in range(1, len(P)):
                            B2[P[i]] = {Y[P[i - 1]]}
                        official = any(all(set(s[i]) == B2[i] for i in range(n)) for s in moves(v, B, rings=False))
                        c['  official' if official else '  NOT OFFICIAL'] += 1
                        J2 = set(range(m)) - set().union(*B2)
                        h, R = hyps(v, B2, f, J2)
                        b2 = [val(v, i, B2[i]) for i in range(n)]
                        c['  (A0) %s, (A1) %s' % (h['A0'], h['A1'])] += 1
                        if len(H0) == 2:
                            c['  |H0| = 2: (A2) %s' % h['A2']] += 1
                        c['  d meets (A3): %s' % (val(v, d, J2) <= b2[d])] += 1
                        if len(H0) != 2:
                            continue
                        xt = P[-1]
                        V1 = [q for q in range(n) if q not in P and q != f and Y[q] is not None
                              and any(i != q and v[i][Y[q]] > b2[i] for i in range(n)) and val(v, q, J2) > pv[q]]
                        V2 = [P[i] for i in range(1, len(P)) if any(j != P[i] and v[j][Y[P[i - 1]]] > b2[j] for j in range(n))
                              and val(v, P[i], J2) > b2[P[i]]]
                        allh = h['A0'] and h['A1'] and h['A2'] and h['A3']
                        c['  ABS\' holds at B\'' if allh else ('  ABS\' fails, (V1) or (V2) present' if (V1 or V2)
                                                             else '  ABS\' FAILS WITHOUT (V1)/(V2)')] += 1
                        for q in V1:
                            if q not in Dfull:
                                c['  (V1) q not in D^full: values Y_xt %s' % (v[q][Y[xt]] > 0)] += 1
                        if allh:
                            X, one = construct(v, B2, f, J2, R, rng)
                            c['  ABS\' construction EFX0' if one and efx0(v, [sorted(x) for x in X]) else '  ABS\' CONSTRUCTION FAILS'] += 1
    for k in sorted(c):
        print('  %-55s %d' % (k, c[k]))

if __name__ == '__main__':
    print('$ python3 k4/referee/absp_ref.py', *sys.argv[1:], flush=True)
    if sys.argv[1] == 'absp':
        absp(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
    else:
        ch(int(sys.argv[2]), int(sys.argv[3]))
