"""Verify a welfare-stranding instance found by w_synth_family.py (kgen/charity.md §6) without z3: rebuild the
hypergraph S'(SIGMA, K) and its stranded state (stuck_family.build), read the values from the log line "values [...]",
and check (1) the state with the raw definitions (EFX0, strong charity), (2) the largest welfare overall and with at
most SIGMA - 2 goods unallocated by chlib.welfare_max (pysat), (3) the same by a MILP (scipy/HiGHS,
w_counterexample.milp_best's formulation, rewritten here for a general instance).

    python3 kgen/charity/w_verify.py SIGMA K LOGFILE"""
import sys, ast, numpy as np
from fractions import Fraction
from scipy.optimize import milp, LinearConstraint, Bounds
from stuck_family import build
from chlib import Inst, welfare_max, efx0, pool_ok, pool_of


def milp_best(V, n, m, maxpool):
    idx = lambda g, a: g * (n + 1) + a
    N = m * (n + 1); A = []; lo = []; hi = []
    for g in range(m):
        row = np.zeros(N); row[[idx(g, a) for a in range(n + 1)]] = 1; A.append(row); lo.append(1); hi.append(1)
    row = np.zeros(N); row[[idx(g, n) for g in range(m)]] = 1; A.append(row); lo.append(0); hi.append(maxpool)
    BIG = sum(sum(d.values()) for d in V) + 1
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            for h in range(m):
                row = np.zeros(N)
                for g, x in V[i].items():
                    row[idx(g, j)] += x; row[idx(g, i)] -= x
                row[idx(h, j)] += BIG - V[i].get(h, 0)
                A.append(row); lo.append(-np.inf); hi.append(BIG)
    c = np.zeros(N)
    for i in range(n):
        for g, x in V[i].items():
            c[idx(g, i)] = -x
    r = milp(c, constraints=LinearConstraint(np.array(A), lo, hi), integrality=np.ones(N), bounds=Bounds(0, 1))
    assert r.status == 0, r.message
    return int(round(-r.fun))


if __name__ == '__main__':
    sigma, K, logf = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    print('$ python3 kgen/charity/w_verify.py', *sys.argv[1:], flush=True)
    line = [l for l in open(logf) if 'values [' in l][0]
    raw = ast.literal_eval(line[line.index('['):].strip())
    I0, X, P, src, ch = build(sigma, K, own=True)
    V = [{int(g): Fraction(x) for g, x in d.items()} for d in raw]
    assert all(set(V[a]) == I0.R[a] for a in range(I0.n)), 'values must live on the hypergraph'
    assert all(x.denominator == 1 for d in V for x in d.values()), 'integer values expected'
    V = [{g: int(x) for g, x in d.items()} for d in V]
    I = Inst(I0.n, I0.m, V)
    wX = sum(I.val(a, X[a]) for a in range(I.n))
    print("S'(%d, %d): n %d, m %d, max |R_i| %d; stranded state EFX0 %s, strong charity %s, welfare %d, %d out" % (
        sigma, K, I.n, I.m, I.k(), efx0(I, X), pool_ok(I, X, P), wX, len(P)), flush=True)
    W, p, Y = welfare_max(I)
    Wf = welfare_max(I, maxpool=sigma - 2)[0]
    print('SAT: largest welfare %d with %d out; with <= %d out: %d' % (W, p, sigma - 2, Wf), flush=True)
    M = milp_best(V, I.n, I.m, I.m); Mf = milp_best(V, I.n, I.m, sigma - 2)
    print('MILP: largest welfare %d; with <= %d out: %d' % (M, sigma - 2, Mf), flush=True)
    assert efx0(I, X) and pool_ok(I, X, P) and W == M == wX and p >= sigma - 1 and Wf == Mf < wX
    print('verified: every welfare maximum leaves at least %d goods unallocated (W(%d, %d) is false)' % (
        sigma - 1, K, sigma - 2))
