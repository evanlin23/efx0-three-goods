"""Two agents, positive generic values, the case of kgen/n3.md §8 left open (neither LPT_a nor LPT_b separates the
picks): which fallback cut-and-choose constructions give shape A1 or B?  F1/F2: an LPT, then move the other agent's
pick across; F3/F4: LPT without one pick, then add it to the bundle without the other pick; F5/F6: LPT with both
picks placed first in different bundles.  'b cuts' = a chooses; 'a cuts' = b chooses.

    python3 kgen/n2_fallback.py SEED N MMIN MMAX"""
import sys, random, collections, json
from oc2 import sd
from n2_rules import shape
from n2_lpt import lpt


def lpt_pre(vc, goods, pre):
    B = [set(), set()]; val = [0, 0]
    for g, s in pre.items(): B[s].add(g); val[s] += vc[g]
    for g in sorted([g for g in goods if g not in pre], key=lambda h: (-vc[h], h)):
        s = 0 if val[0] <= val[1] else 1
        B[s].add(g); val[s] += vc[g]
    return B


def choose(v, P, Q, cutter, chooser):
    X = [None, None]
    if sum(v[chooser][g] for g in P) >= sum(v[chooser][g] for g in Q): X[chooser], X[cutter] = set(P), set(Q)
    else: X[chooser], X[cutter] = set(Q), set(P)
    return X


if __name__ == '__main__':
    seed, N, lo, hi = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter(); ex = {}
    print('$ python3 kgen/n2_fallback.py', *sys.argv[1:], flush=True)
    for t in range(N):
        m = rng.randint(lo, hi); v = [rng.sample(range(1, 10 ** 6), m) for _ in range(2)]
        for a, b in [(0, 1), (1, 0)]:
            y = sd(v, (a, b)); ya, yb = y[a], y[b]
            sep = lambda B: (ya in B[0]) != (yb in B[0])
            if v[b][ya] > v[b][yb] or sep(lpt(v[b], range(m))) or sep(lpt(v[a], range(m))): continue
            C['open-case starts'] += 1
            cands = {}
            P, Q = lpt(v[b], range(m)); Z, W = (P, Q) if yb in P else (Q, P)
            cands['F1 b-LPT, move y_a to the other bundle (a chooses)'] = choose(v, Z - {ya}, W | {ya}, b, a)
            P, Q = lpt(v[a], range(m)); Z, W = (P, Q) if ya in P else (Q, P)
            cands['F2 a-LPT, move y_b to the other bundle (b chooses)'] = choose(v, Z - {yb}, W | {yb}, a, b)
            P, Q = lpt(v[b], [g for g in range(m) if g != ya]); Z, W = (P, Q) if yb in P else (Q, P)
            cands['F3 b-LPT without y_a, then y_a away from y_b (a chooses)'] = choose(v, Z, W | {ya}, b, a)
            P, Q = lpt(v[a], [g for g in range(m) if g != yb]); Z, W = (P, Q) if ya in P else (Q, P)
            cands['F4 a-LPT without y_b, then y_b away from y_a (b chooses)'] = choose(v, Z, W | {yb}, a, b)
            P, Q = lpt_pre(v[b], range(m), {yb: 0, ya: 1})
            cands['F5 b-LPT with the picks placed first (a chooses)'] = choose(v, P, Q, b, a)
            P, Q = lpt_pre(v[a], range(m), {ya: 0, yb: 1})
            cands['F6 a-LPT with the picks placed first (b chooses)'] = choose(v, P, Q, a, b)
            okany = False
            for k, X in cands.items():
                s = shape(v, X, ya, yb, a, b); ok = s in ('A1', 'B'); okany |= ok
                C[k + ': ok' if ok else k + ': fails'] += 1
                if not ok and k not in ex: ex[k] = (v, (a, b))
            C['some fallback works'] += okany
            if not okany and 'none' not in ex: ex['none'] = (v, (a, b))
    for k in sorted(C): print(k, C[k])
    for k, e in ex.items(): print('first failure', k, json.dumps(e))
