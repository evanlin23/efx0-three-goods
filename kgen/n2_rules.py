"""Two agents: candidate constructions for the shapes "A1 or B" (kgen/n3.md §4), tested on random instances with zeros.
a = first picker (y_a its top), b = second (y_b its top without y_a).  Each rule: b cuts M into (P, Q), a takes its
favourite (ties to the bundle with y_a), then every good of a's bundle that a values at 0 moves to b (Lemma M).
The result must be EFX0 and of shape A1 or B (checked from the definitions).

    python3 kgen/n2_rules.py SEED N MMIN MMAX"""
import sys, random, itertools, json, collections
from oc2 import efx0, sd, gen


def shape(v, X, ya, yb, a, b):
    """A1 / B for the final allocation X (lists indexed by agent), or None"""
    m = len(v[0]); R = [{g for g in range(m) if v[i][g] > 0} for i in range(2)]
    J = set(range(m)) - {ya, yb}
    if not efx0(v, X): return 'NOT EFX0'
    if ya in X[a] and (yb is None or yb in X[b]) and len(X[a] - R[a]) <= 1: return 'A1'
    if ya in X[b]:
        H1 = X[b] & J & R[b]
        if v[b][ya] + sum(v[b][g] for g in H1) > (v[b][yb] if yb is not None else 0):
            pool = J | ({yb} if yb is not None else set())
            H0 = X[a] & pool & R[a]
            if sum(v[a][g] for g in H0) > v[a][ya]:
                if len(X[a] - H0) <= 1 or len(X[b] - H1 - {ya}) <= 1: return 'B'
    return None


def lpt(vb, goods, pre=None):
    """b's greedy: goods in decreasing v_b to the poorer bundle (ties to P); pre = {good: 0 or 1} pre-placed"""
    B = [set(), set()]; val = [0, 0]
    for g, s in (pre or {}).items(): B[s].add(g); val[s] += vb[g]
    for g in sorted([g for g in goods if g not in (pre or {})], key=lambda h: (-vb[h], h)):
        s = 0 if val[0] <= val[1] else 1
        B[s].add(g); val[s] += vb[g]
    return B


def feasible_b(vb, P, Q):
    def ok(A, Bn):  # holder of A does not strongly envy Bn
        return len(Bn) < 2 or sum(vb[g] for g in A) >= sum(vb[g] for g in Bn) - min(vb[g] for g in Bn)
    return ok(P, Q) and ok(Q, P)


def finish(v, P, Q, a, b, ya):
    va = v[a]
    take = P if (sum(va[g] for g in P) > sum(va[g] for g in Q) or (sum(va[g] for g in P) == sum(va[g] for g in Q) and ya in P)) else Q
    other = Q if take is P else P
    Xa = {g for g in take if va[g] > 0}; Xb = set(other) | {g for g in take if va[g] == 0}
    X = [None, None]; X[a] = Xa; X[b] = Xb
    return X


RULES = {}


def rule(f):
    RULES[f.__name__] = f; return f


@rule
def lpt_plain(v, a, b, ya, yb):
    P, Q = lpt(v[b], range(len(v[0])))
    return P, Q


@rule
def lpt_ya(v, a, b, ya, yb):
    return tuple(lpt(v[b], range(len(v[0])), {ya: 0}))


@rule
def lpt_sep(v, a, b, ya, yb):
    return tuple(lpt(v[b], range(len(v[0])), {ya: 0, yb: 1} if yb is not None else {ya: 0}))


@rule
def best_feasible(v, a, b, ya, yb):
    """every b-feasible partition, a chooses; first one whose outcome has shape A1/B (an existence check, not a rule)"""
    m = len(v[0])
    for asg in itertools.product(range(2), repeat=m):
        P = {g for g in range(m) if asg[g] == 0}; Q = set(range(m)) - P
        if feasible_b(v[b], P, Q):
            X = finish(v, P, Q, a, b, ya)
            if shape(v, X, ya, yb, a, b) in ('A1', 'B'): return P, Q
    return set(range(m)), set()


if __name__ == '__main__':
    seed, N, lo, hi = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter(); ex = {}
    print('$ python3 kgen/n2_rules.py', *sys.argv[1:], flush=True)
    for t in range(N):
        m = rng.randint(lo, hi); v = gen(rng, m)
        for a, b in [(0, 1), (1, 0)]:
            y = sd(v, (a, b)); ya, yb = y[a], y[b]
            C['starts'] += 1
            for name, f in RULES.items():
                P, Q = f(v, a, b, ya, yb)
                X = finish(v, P, Q, a, b, ya)
                s = shape(v, X, ya, yb, a, b)
                C['%s: %s' % (name, s)] += 1
                if s not in ('A1', 'B') and name not in ex: ex[name] = (v, (a, b), [sorted(P), sorted(Q)], s)
    for k in sorted(C): print(k, C[k])
    for k, e in ex.items(): print('first failure', k, json.dumps(e, default=list))
