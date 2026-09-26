"""Encoding B: a second, independently written exact test of Output(s, o, .) (lean/EFX/LB4R.lean), as a MILP
with pseudo-Boolean rows. Shares no code with lb4r.build_model: its own needs, NA, frozen and omega, OC written
directly from the definition (one row per agent j != o and removed good h), frozen status two-sided.

State s = (base, pick, marked) as in lb4r.py; values v[i][g] nonnegative ints.
"""
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix


def _needs(v, s):
    base, pick, marked = s
    n, m = len(v), len(v[0])
    out = []
    for i in range(n):
        Bi = [g for g in range(m) if base[g] == i]
        if marked[i]:
            vb = sum(v[i][g] for g in Bi)
            out.append({g for g in range(m) if base[g] != i and v[i][g] > vb})
        elif pick[i] == -1:
            out.append({g for g in range(m) if v[i][g] > 0})
        else:
            out.append({g for g in range(m) if v[i][g] > 0 and v[i][g] > v[i][pick[i]]})
    return out


def output_b(v, s, o, conv):
    """Is there X with Output(s, o, X)? conv 'bundle' (owner needs from bundle, Lean) or 'base'."""
    base = s[0]
    n, m = len(v), len(v[0])
    N = _needs(v, s)
    B = [[g for g in range(m) if base[g] == i] for i in range(n)]
    J = [g for g in range(m) if base[g] == -1]
    NAall = set().union(*N)
    # omega = |J| - sum of signed caps (cap 0 for a frozen agent)
    capsum = sum(0 if (len(B[i]) == 1 and B[i][0] in NAall) else 2 - len(B[i]) for i in range(n))
    om = len(J) - capsum
    if max(len(b) for b in B) <= 2 and ((o is None) != (om <= 0)):
        return False
    # needs of agents other than the owner (unchanged under ownerNeeds)
    if o is None or conv == "base":
        fixedNA = NAall
    else:
        fixedNA = set().union(*[N[i] for i in range(n) if i != o]) if n > 1 else set()
    if o is not None and len(B[o]) == 1 and B[o][0] in fixedNA:
        return False  # owner frozen (its own needs from its bundle never contain its base good)
    if o is not None and conv == "base" and len(B[o]) == 1 and B[o][0] in NAall:
        return False
    others = [j for j in range(n) if j != o]
    # variables: y[g] (g in X_o), z[g,j] (g in C_j), f[j] (frozen)
    idx = {}

    def var(key):
        if key not in idx:
            idx[key] = len(idx)
        return idx[key]
    for g in J:
        if o is not None:
            var(("y", g))
        for j in others:
            var(("z", g, j))
    for j in others:
        var(("f", j))
    rows = []  # (dict var->coef, lo, hi)
    for g in J:
        d = {var(("z", g, j)): 1 for j in others}
        if o is not None:
            d[var(("y", g))] = 1
        rows.append((d, 1, 1))
    vo_base = sum(v[o][g] for g in B[o]) if o is not None else 0
    for j in others:
        f = var(("f", j))
        if len(B[j]) != 1:
            rows.append(({f: 1}, 0, 0))
        else:
            yj = B[j][0]
            if yj in fixedNA:
                rows.append(({f: 1}, 1, 1))
            elif conv == "base" or o is None:
                rows.append(({f: 1}, 0, 0))
            else:
                # f = 1  <=>  v_o(X_o) < v_o(yj)   (N_o^X contains yj; X yj = j != o)
                M = sum(v[o]) + v[o][yj] + 1
                d = {var(("y", g)): v[o][g] for g in J if v[o][g] > 0}
                # v_o(X_o) + M f >= v_o(yj)
                d1 = dict(d)
                d1[f] = d1.get(f, 0) + M
                rows.append((d1, v[o][yj] - vo_base, np.inf))
                # v_o(X_o) <= v_o(yj) - 1 + M (1 - f)   i.e.  v_o(X_o) + M f <= v_o(yj) - 1 + M
                d2 = dict(d)
                d2[f] = d2.get(f, 0) + M
                rows.append((d2, -np.inf, v[o][yj] - 1 + M - vo_base))
        # junk count: sum z <= (2 - |B_j|) (1 - f)  ->  sum z + (2 - |B_j|) f <= 2 - |B_j|
        c = 2 - len(B[j])
        d = {var(("z", g, j)): 1 for g in J}
        if c != 0:
            d[f] = d.get(f, 0) + c
        rows.append((d, -np.inf, c))
        # frozen => no junk (also covers c < 0 and f = 1): sum z <= |J| (1 - f)
        d = {var(("z", g, j)): 1 for g in J}
        d[f] = d.get(f, 0) + len(J)
        rows.append((d, -np.inf, len(J)))
    # OC: for j != o and h in X_o: v_j(X_o) - v_j(h) <= v_j(X_j)
    if o is not None:
        for j in others:
            vjBo = sum(v[j][g] for g in B[o])
            vjBj = sum(v[j][g] for g in B[j])
            M = sum(v[j]) + 1
            lin = {}
            for g in J:
                if v[j][g]:
                    lin[var(("y", g))] = lin.get(var(("y", g)), 0) + v[j][g]
                    lin[var(("z", g, j))] = lin.get(var(("z", g, j)), 0) - v[j][g]
            # h in B_o: always in X_o
            for h in B[o]:
                rows.append((dict(lin), -np.inf, vjBj - vjBo + v[j][h]))
            # h junk: lin - v_j(h) <= vjBj - vjBo + M (1 - y_h)  ->  lin + M y_h <= vjBj - vjBo + v_j(h) + M
            for h in J:
                d = dict(lin)
                d[var(("y", h))] = d.get(var(("y", h)), 0) + M
                rows.append((d, -np.inf, vjBj - vjBo + v[j][h] + M))
    nv = len(idx) + 1
    A = lil_matrix((max(len(rows), 1), nv))
    lo = np.full(max(len(rows), 1), -np.inf)
    hi = np.full(max(len(rows), 1), np.inf)
    for r, (d, a, b) in enumerate(rows):
        for k, c in d.items():
            A[r, k] = c
        lo[r], hi[r] = a, b
    res = milp(c=np.zeros(nv), constraints=[LinearConstraint(A.tocsr(), lo, hi)], integrality=np.ones(nv),
               bounds=Bounds(0, 1))
    if res.status == 2:
        return False
    if res.status != 0:
        raise RuntimeError(res.message)
    return True
