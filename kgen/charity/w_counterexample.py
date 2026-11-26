"""Proposition CH-F (kgen/charity.md §6): W(4, 1) and W(3, 1) are false.  Two instances whose welfare maximum over
partial EFX0 allocations leaves two goods unallocated:
  k4: S'(3, 4)'s hypergraph, n = 9, m = 14, every agent valuing at most four goods, integer values <= 40;
  k3: S'(3, 3)'s hypergraph (with relays), n = 12, m = 17, every agent valuing at most three goods, values <= 60.
The values were found by w_synth_family.py (z3); this script checks each instance three ways, none of them z3:
  1. the stranded state X by the raw definitions (EFX0, strong charity), own code;
  2. the largest welfare over EFX0 allocations leaving <= 1 good out, and leaving 0 out, by chlib.welfare_max
     (pysat CaDiCaL, reachable-partial-sums encoding);
  3. the same two numbers by a mixed-integer program written here (scipy.optimize.milp, HiGHS), with the EFX0
     constraints in big-M form.
Goods: x_j = 2j, x'_j = 2j + 1 (j = 0, 1, 2), pool goods g_0 = 6, g_1 = 7, champion goods y_{g,j} = 8 + 2j + g, and
(k3) relay goods 14, 15, 16.

    python3 kgen/charity/w_counterexample.py [k4|k3]"""
import itertools
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds

V4 = [{0: 20, 6: 21, 8: 40},              # c(g0, j0): holds y = 8
     {0: 12, 7: 16, 9: 27},              # c(g1, j0): holds 9
     {2: 20, 6: 21, 10: 40},             # c(g0, j1): holds 10
     {2: 12, 7: 13, 11: 24},             # c(g1, j1): holds 11
     {4: 20, 6: 21, 12: 40},             # c(g0, j2): holds 12
     {4: 9, 7: 10, 13: 18},              # c(g1, j2): holds 13
     {0: 2, 1: 1, 12: 7, 13: 4},         # s0: holds {0, 1}; its children are the champions c(., j2)
     {2: 2, 3: 1, 8: 5, 9: 4},           # s1: holds {2, 3}; children c(., j0)
     {4: 2, 5: 1, 10: 8, 11: 4}]         # s2: holds {4, 5}; children c(., j1)
X4 = [{8}, {9}, {10}, {11}, {12}, {13}, {0, 1}, {2, 3}, {4, 5}]
V3 = [{0: 18, 6: 20, 8: 37}, {0: 28, 7: 33, 9: 60}, {2: 15, 6: 16, 10: 30}, {2: 30, 7: 31, 11: 60},
      {4: 25, 6: 24, 12: 48}, {4: 32, 7: 29, 13: 60},       # champions c(g, j), holding 8 + 2j + g
      {12: 59, 13: 60, 14: 58},                             # relay above c(., j2), holds 14
      {0: 2, 1: 1, 14: 4},                                  # s0, holds {0, 1}
      {8: 59, 9: 60, 15: 58},                               # relay above c(., j0), holds 15
      {2: 2, 3: 1, 15: 4},                                  # s1, holds {2, 3}
      {10: 59, 11: 60, 16: 58},                             # relay above c(., j1), holds 16
      {4: 8, 5: 1, 16: 10}]                                 # s2, holds {4, 5}
X3 = [{8}, {9}, {10}, {11}, {12}, {13}, {14}, {0, 1}, {15}, {2, 3}, {16}, {4, 5}]
import sys as _sys
WHICH = _sys.argv[1] if len(_sys.argv) > 1 else 'k4'
V, X = (V4, X4) if WHICH == 'k4' else (V3, X3)
n, m, POOL = len(V), (14 if WHICH == 'k4' else 17), {6, 7}
K = 4 if WHICH == 'k4' else 3


def val(i, B):
    return sum(V[i].get(g, 0) for g in B)


def efx0(Y):
    for i in range(n):
        for j in range(n):
            if i != j and Y[j] and val(i, Y[j]) - min(V[i].get(h, 0) for h in Y[j]) > val(i, Y[i]):
                return False
    return True


def milp_best(maxpool):
    """max sum_i v_i(Y_i) over EFX0 allocations Y with at most maxpool goods unallocated (x[g][a], a = n: pool)."""
    idx = lambda g, a: g * (n + 1) + a
    N = m * (n + 1); A = []; lo = []; hi = []
    for g in range(m):                                   # each good exactly once
        row = np.zeros(N); row[[idx(g, a) for a in range(n + 1)]] = 1; A.append(row); lo.append(1); hi.append(1)
    row = np.zeros(N); row[[idx(g, n) for g in range(m)]] = 1; A.append(row); lo.append(0); hi.append(maxpool)
    BIG = sum(sum(d.values()) for d in V) + 1
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            for h in range(m):                           # x[h][j] = 1  =>  v_i(Y_j) - v_i(h) <= v_i(Y_i)
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
    if r.status != 0:
        return None, r.message
    Y = [{g for g in range(m) if r.x[idx(g, a)] > 0.5} for a in range(n)]
    assert efx0(Y)
    return int(round(-r.fun)), Y


if __name__ == '__main__':
    print('$ python3 kgen/charity/w_counterexample.py', WHICH)
    assert all(len(d) <= K for d in V) and set().union(*X) | POOL == set(range(m))
    print('instance %s: n %d, m %d, every agent values at most %d goods' % (WHICH, n, m, K))
    wX = sum(val(i, X[i]) for i in range(n))
    print('stranded state: EFX0 %s, strong charity %s, welfare %d, unallocated %s' % (
        efx0(X), all(val(i, POOL) <= val(i, X[i]) for i in range(n)), wX, sorted(POOL)))
    import sys, os
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from chlib import Inst, welfare_max, efx0 as efx0_lib
    I = Inst(n, m, V)
    W, p, Y = welfare_max(I)
    W1 = welfare_max(I, maxpool=1)[0]; W0 = welfare_max(I, maxpool=0)[0]
    print('SAT (chlib.welfare_max): largest welfare %d with %d unallocated; <= 1 unallocated: %d; complete: %d' % (
        W, p, W1, W0))
    M1, Y1 = milp_best(1); M0, Y0 = milp_best(0); M2, Y2 = milp_best(m)
    print('MILP (HiGHS): largest welfare %d; <= 1 unallocated: %d; complete: %d' % (M2, M1, M0))
    assert efx0(X) and W == M2 == wX and p >= 2 and W1 == M1 < wX and W0 == M0 < wX
    print('verified: every welfare maximum leaves at least two goods unallocated (W(%d, 1) is false)' % K)
