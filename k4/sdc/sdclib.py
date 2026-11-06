"""SAT climb to Pareto-maximal partial EFX0 allocations; check P1: each such maximum (with the most goods allocated for
its value vector) is complete.  Instance: sets[i] (goods), vals[i] (values, same order), m goods."""
import sys, os, json, random, itertools
from pysat.solvers import Minisat22, Cadical153
from pysat.card import CardEnc, EncType

def subsets(xs):
    xs = list(xs)
    for r in range(len(xs) + 1):
        yield from itertools.combinations(xs, r)

class Enc:
    def __init__(self, sets, vals, m, slack=0):
        self.n = n = len(sets); self.m = m
        self.R = [list(s) for s in sets]
        self.v = [dict(zip(s, vv)) for s, vv in zip(sets, vals)]
        self.top = 0
        self.x = [[self.new() for a in range(n + 1)] for g in range(m)]  # a = n is the pool
        self.cl = []
        for g in range(m):
            self.cl.append([self.x[g][a] for a in range(n + 1)])
            for a in range(n + 1):
                for b in range(a + 1, n + 1):
                    self.cl.append([-self.x[g][a], -self.x[g][b]])
        self.y = []
        for i in range(n):
            Ri = self.R[i]; d = {}
            for S in subsets(Ri):
                y = self.new(); d[S] = y
                for g in Ri:
                    self.cl.append([-y, self.x[g][i] if g in S else -self.x[g][i]])
                self.cl.append([y] + [-self.x[g][i] for g in S] + [self.x[g][i] for g in Ri if g not in S])
            self.y.append(d)
        # EFX0 constraints
        for i in range(n):
            vi = self.v[i]; Ri = self.R[i]
            for S, y in self.y[i].items():
                vs = sum(vi[g] for g in S)
                rest = [g for g in Ri if g not in S]
                # minimal T subset of rest with v(T) > vs
                Ts = [T for T in subsets(rest) if T and sum(vi[g] for g in T) > vs - slack]
                Ts = [T for T in Ts if not any(set(U) < set(T) for U in Ts)]
                for j in range(n):
                    if j == i: continue
                    for T in Ts:
                        for h in range(m):
                            if h in T: continue
                            self.cl.append([-y] + [-self.x[g][j] for g in T] + [-self.x[h][j]])
    def new(self):
        self.top += 1; return self.top
    def val(self, i, S):
        return sum(self.v[i].get(g, 0) for g in S)

def decode(E, model):
    pos = set(l for l in model if l > 0)
    asg = []
    for g in range(E.m):
        for a in range(E.n + 1):
            if E.x[g][a] in pos: asg.append(a); break
    return asg

def values(E, asg):
    return tuple(sum(E.v[i].get(g, 0) for g, a in enumerate(asg) if a == i) for i in range(E.n))

def improve(E, asg, rng=None):
    """Find a partial EFX0 allocation with values >= and (some value > or more goods allocated)."""
    u = values(E, asg); A = sum(1 for a in asg if a < E.n)
    cl = list(E.cl); top = E.top
    def new():
        nonlocal top; top += 1; return top
    zs = []
    for i in range(E.n):
        for S, y in E.y[i].items():
            if E.val(i, S) < u[i]: cl.append([-y])
        z = new(); zs.append(z)
        cl.append([-z] + [y for S, y in E.y[i].items() if E.val(i, S) > u[i]])
    w = new()
    if A < E.m:
        pool = [E.x[g][E.n] for g in range(E.m)]
        card = CardEnc.atmost(lits=pool, bound=E.m - A - 1, top_id=top, encoding=EncType.seqcounter)
        top = max(top, card.nv)
        for c in card.clauses: cl.append(c + [-w])
        cl.append(zs + [w])
    else:
        cl.append(zs)
    s = Cadical153(bootstrap_with=cl)
    ok = s.solve()
    res = decode(E, s.get_model()) if ok else None
    s.delete()
    return res

def climb(E, rng, start=None):
    asg = start if start is not None else [E.n] * E.m
    steps = 0
    while True:
        nxt = improve(E, asg)
        if nxt is None: return asg, steps
        asg = nxt; steps += 1

def random_start(E, rng, tries=50):
    # random partial EFX0 allocation: random singletons
    asg = [E.n] * E.m
    goods = list(range(E.m)); rng.shuffle(goods)
    for g in goods:
        a = rng.randrange(E.n + 1)
        asg[g] = a
        B = [[h for h in range(E.m) if asg[h] == i] for i in range(E.n)]
        if not efx0(E, B): asg[g] = E.n
    return asg

def efx0(E, B):
    for i in range(E.n):
        own = E.val(i, B[i])
        for j in range(E.n):
            if j == i or len(B[j]) < 2: continue
            vals = [E.v[i].get(g, 0) for g in B[j]]
            if sum(vals) - min(vals) > own: return False
    return True

if __name__ == '__main__':
    pass
