"""Two agents: do cut-and-choose outcomes suffice for OC1(t >= 0)?  For every start, every cutter (a or b), every
feasible partition of the cutter (EFX0 for it both ways), the chooser takes its favourite (both on ties) and its
worthless goods move to the cutter (Lemma M); count starts where some outcome has a shape A1, A2, B or C
(kgen/n3.md section 4).  Fixed seed 1, 500 instances, m = 3..10.

    python3 kgen/n2_cutchoose.py"""
import sys, random, itertools, collections, json
sys.path.insert(0, '/home/user/efx0-three-goods/kgen')
from oc2 import efx0, sd, gen
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
def feas(vc, P, Q):
    ok = lambda A, B: len(B) < 2 or sum(vc[g] for g in A) >= sum(vc[g] for g in B) - min(vc[g] for g in B)
    return ok(P, Q) and ok(Q, P)
rng = random.Random(1); C = collections.Counter(); ex = None
for t in range(500):
    m = rng.randint(3, 10); v = gen(rng, m)
    for a, b in [(0, 1), (1, 0)]:
        y = sd(v, (a, b)); ya, yb = y[a], y[b]; C['starts'] += 1; got = set()
        for cutter in (a, b):
            ch = 1 - cutter
            for asg in itertools.product(range(2), repeat=m):
                P = {g for g in range(m) if asg[g] == 0}; Q = set(range(m)) - P
                if not feas(v[cutter], P, Q): continue
                vp, vq = sum(v[ch][g] for g in P), sum(v[ch][g] for g in Q)
                for take in ([P] if vp > vq else [Q] if vq > vp else [P, Q]):
                    other = Q if take is P else P
                    X = [None, None]
                    X[ch] = {g for g in take if v[ch][g] > 0}; X[cutter] = set(other) | {g for g in take if v[ch][g] == 0}
                    s = shapes4(v, X, ya, yb, a, b)
                    if s: got.add('cutter ' + ('a' if cutter == a else 'b'))
        for k in got: C[k] += 1
        if got: C['some cutter'] += 1
        elif ex is None: ex = (v, (a, b))
for k in sorted(C): print(k, C[k])
print('uncovered example', json.dumps(ex))
