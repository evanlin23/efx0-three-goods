"""Two agents, strictly positive generic values: the LPT cut-and-choose argument of kgen/n3.md §8.
a = first picker, b = second.  Case 2: b values y_a above y_b -> b's LPT (descending v_b, to the poorer bundle) separates
y_a and y_b.  Case 1 (b values y_b above y_a): if b's LPT separates the picks, b cuts and a chooses; else if a's LPT
(descending v_a) separates them, a cuts and b chooses.  Each outcome must be EFX0 and of shape A1 or B (checked from the
definitions).  Reports how often neither LPT separates the picks, and whether any EFX0 allocation of shape A1/B exists
then (always, by kgen/shapes2.py's data).

    python3 kgen/n2_lpt.py SEED N MMIN MMAX"""
import sys, random, itertools, collections, json
from oc2 import efx0, sd
from n2_rules import shape


def lpt(vc, goods):
    B = [set(), set()]; val = [0, 0]
    for g in sorted(goods, key=lambda h: (-vc[h], h)):
        s = 0 if val[0] <= val[1] else 1
        B[s].add(g); val[s] += vc[g]
    return B


def cut_choose(v, cutter, chooser):
    P, Q = lpt(v[cutter], range(len(v[0])))
    vp, vq = sum(v[chooser][g] for g in P), sum(v[chooser][g] for g in Q)
    X = [None, None]
    if vp >= vq: X[chooser], X[cutter] = P, Q
    else: X[chooser], X[cutter] = Q, P
    return X, (P, Q)


if __name__ == '__main__':
    seed, N, lo, hi = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter(); ex = []
    print('$ python3 kgen/n2_lpt.py', *sys.argv[1:], flush=True)
    for t in range(N):
        m = rng.randint(lo, hi)
        v = [rng.sample(range(1, 10 ** 6), m) for _ in range(2)]   # positive, generic
        for a, b in [(0, 1), (1, 0)]:
            y = sd(v, (a, b)); ya, yb = y[a], y[b]; C['starts'] += 1
            sepb = lambda: (lambda B: (ya in B[0]) != (yb in B[0]))(lpt(v[b], range(m)))
            sepa = lambda: (lambda B: (ya in B[0]) != (yb in B[0]))(lpt(v[a], range(m)))
            case = 2 if v[b][ya] > v[b][yb] else 1
            C['case %d' % case] += 1
            if case == 2 or sepb():
                X, _ = cut_choose(v, b, a); s = shape(v, X, ya, yb, a, b); C['b cuts: %s' % s] += 1
            elif sepa():
                X, _ = cut_choose(v, a, b); s = shape(v, X, ya, yb, a, b); C['a cuts: %s' % s] += 1
            else:
                C['neither LPT separates the picks'] += 1
                Xs = [[{g for g in range(m) if q[g] == i} for i in range(2)] for q in itertools.product(range(2), repeat=m)]
                ok = [X for X in Xs if shape(v, X, ya, yb, a, b) in ('A1', 'B')]
                C['  ... some A1/B allocation exists: %s' % bool(ok)] += 1
                if len(ex) < 3: ex.append((v, (a, b), [sorted(X[a]) for X in ok[:2]], [shape(v, X, ya, yb, a, b) for X in ok[:2]]))
    for k in sorted(C): print(k, C[k])
    for e in ex: print('neither separates:', json.dumps(e))
