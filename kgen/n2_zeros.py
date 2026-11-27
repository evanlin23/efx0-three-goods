"""Lemma 2 with zero values (kgen/n3.md §8): two agents, values positive-generic on each agent's relevant goods but
possibly 0.  Construction:
  (i)/(ii) (b values y_a above y_b, or LPT_b separates the picks): b cuts by LPT_b (zero goods last, all to the
           poorer bundle), a chooses, then a's worthless goods move to b (Lemma M);
  (iii) (LPT_a separates the picks): a cuts by LPT_a, b chooses, then b's worthless goods move to a;
  open case: the ratio knife (b takes junk by v_b/v_a decreasing, a-worthless goods first, b-worthless last), then
           a's worthless goods move to b when a envies nobody.
Target: an OC1(t >= 0) shape (A1, A2, B or C; kgen/n2_cutchoose.py's shapes4), checked from the definitions.

    python3 kgen/n2_zeros.py SEED N MMIN MMAX"""
import sys, random, collections, json, itertools
from oc2 import efx0, sd

sys.path.insert(0, '/tmp')


def shapes4(v, X, ya, yb, a, b):
    m = len(v[0]); R = [{g for g in range(m) if v[i][g] > 0} for i in range(2)]; J = set(range(m)) - {ya, yb}
    if not efx0(v, X): return set()
    out = set(); y = {a: ya, b: yb}
    if ya in X[a] and (yb is None or yb in X[b]):
        if len(X[a] - R[a]) <= 1: out.add('A1')
        if len(X[b] - R[b]) <= 1: out.add('A2')
    for x0, nm in ((a, 'B'), (b, 'C')):
        x1 = 1 - x0
        if y[x0] is None or y[x0] not in X[x1]: continue
        H1 = X[x1] & J & R[x1]
        if v[x1][y[x0]] + sum(v[x1][g] for g in H1) <= (v[x1][y[x1]] if y[x1] is not None else 0): continue
        H0 = X[x0] & (J | ({y[x1]} if y[x1] is not None else set())) & R[x0]
        if sum(v[x0][g] for g in H0) <= v[x0][y[x0]]: continue
        if len(X[x0] - H0) <= 1 or len(X[x1] - H1 - {y[x0]}) <= 1: out.add(nm)
    return out


def lpt0(vc, goods):
    B = [set(), set()]; val = [0, 0]
    for g in sorted(goods, key=lambda h: (-vc[h], h)):
        s = 0 if val[0] <= val[1] else 1
        B[s].add(g); val[s] += vc[g]
    return B


def choose_move(v, P, Q, cutter, chooser):
    X = [None, None]
    vp, vq = sum(v[chooser][g] for g in P), sum(v[chooser][g] for g in Q)
    take = P if vp >= vq else Q; other = Q if take is P else P
    X[chooser] = {g for g in take if v[chooser][g] > 0}; X[cutter] = set(other) | {g for g in take if v[chooser][g] == 0}
    return X


def knife0(v, a, b, ya, yb, J):
    key = lambda g: (0 if v[a][g] == 0 and v[b][g] > 0 else 1, -(v[b][g] / v[a][g]) if v[a][g] > 0 else 0, g)
    order = sorted(J, key=key)
    for s in range(len(order) + 1):
        Xb = {yb} | set(order[:s]); Xa = {ya} | set(order[s:])
        va_ = [v[b][g] for g in Xa]
        if len(Xa) < 2 or sum(v[b][g] for g in Xb) >= sum(va_) - min(va_):
            X = [None, None]; X[a], X[b] = Xa, Xb
            # Lemma M: a's worthless goods to b when a envies nobody
            if sum(v[a][g] for g in Xa) >= sum(v[a][g] for g in Xb):
                W = {g for g in Xa if v[a][g] == 0}; X[a] = Xa - W; X[b] = Xb | W
            return X


def gen0(rng, m):
    while True:
        v = []
        for i in range(2):
            r = [0] * m; S = [g for g in range(m) if rng.random() < 0.65]
            for g, x in zip(S, rng.sample(range(1, 10 ** 6), len(S))): r[g] = x
            v.append(r)
        if all(v[0][g] or v[1][g] for g in range(m)) and any(v[0]) and any(v[1]): return v


if __name__ == '__main__':
    seed, N, lo, hi = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter(); ex = []
    print('$ python3 kgen/n2_zeros.py', *sys.argv[1:], flush=True)
    for t in range(N):
        m = rng.randint(lo, hi); v = gen0(rng, m)
        for a, b in [(0, 1), (1, 0)]:
            y = sd(v, (a, b)); ya, yb = y[a], y[b]
            if yb is None: C['y_b missing (skipped)'] += 1; continue
            J = [g for g in range(m) if g not in (ya, yb)]
            sep = lambda B: (ya in B[0]) != (yb in B[0])
            if v[b][ya] > v[b][yb] or sep(lpt0(v[b], range(m))):
                case = '(i)/(ii)'; P, Q = lpt0(v[b], range(m)); X = choose_move(v, P, Q, b, a)
            elif sep(lpt0(v[a], range(m))):
                case = '(iii)'; P, Q = lpt0(v[a], range(m)); X = choose_move(v, P, Q, a, b)
            else:
                case = 'open (knife)'; X = knife0(v, a, b, ya, yb, J)
            sh = shapes4(v, X, ya, yb, a, b)
            C['case %s' % case] += 1; C['case %s: OC1 shape' % case] += bool(sh)
            if not sh and len(ex) < 4: ex.append((case, v, (a, b), [sorted(x) for x in X]))
    for k in sorted(C): print(k, C[k])
    for e in ex: print('fails', json.dumps(e))
