"""Exact realizability of strict comparisons by positive additive values (k4/ksens.md §8; used by kcegar.py for agents
with six or more goods, where the strict order types are too many to list).

Question: given integer rows a_1, ..., a_r in Z^d (each a = 1_S - 1_T for disjoint sets S, T, possibly negated), is
there v in R^d with v > 0 and a_j . v > 0 for every j?  The system is homogeneous, so it is equivalent to
    v_g >= 1 for every g,  a_j . v >= 1 for every j.
Solved by a Phase-I simplex over Fractions (Bland's rule, so no cycling) on x = v - 1 >= 0:  a_j . x - s_j = 1 - a_j . 1.

- Feasible: returns an integer vector v in the open cone with all subset sums distinct (v scaled by K = 2^(d+1) and
  perturbed by 2^g: a_j . v changes by less than 2^d < K, and distinct subsets get distinct sums), so the profile is
  strict.
- Infeasible: returns a core, a set of row indices whose rows alone are already infeasible: the rows with a positive
  dual value in the final Phase-I tableau (a Farkas certificate: a nonnegative combination of those rows and of unit
  vectors is zero or negative).  The core is re-checked by a second LP call before it is returned.

    python3 k4/ksens/ratlp.py          self-test against the type lists of kcegar.reps (d <= 5)"""
from fractions import Fraction as F
import itertools, random


def _phase1(rows, d):
    """minimize the sum of artificials; returns (optimum, tableau info)"""
    r = len(rows); b = [1 - sum(a) for a in rows]
    # columns: x_0..x_{d-1}, s_0..s_{r-1}, then one artificial per row with b > 0
    art = [j for j in range(r) if b[j] > 0]; na = len(art); ncol = d + r + na
    T = []; basis = []
    for j, a in enumerate(rows):
        row = [F(0)] * (ncol + 1)
        for g in range(d): row[g] = F(a[g])
        row[d + j] = F(-1); row[ncol] = F(b[j])
        if b[j] > 0:
            k = art.index(j); row[d + r + k] = F(1); basis.append(d + r + k)
        else:                        # s_j = a.x - b >= 0 at x = 0: make s_j basic (multiply the row by -1)
            row = [-x for x in row]; basis.append(d + j)
        T.append(row)
    # objective: minimize sum of artificials = maximize -sum; reduced costs z_c = sum over artificial rows
    obj = [F(0)] * (ncol + 1)
    for i, bv in enumerate(basis):
        if bv >= d + r:
            for c in range(ncol + 1): obj[c] += T[i][c]
    for k in range(na): obj[d + r + k] = F(0)
    while True:
        enter = next((c for c in range(ncol) if obj[c] > 0), None)      # Bland: smallest improving column
        if enter is None: break
        best = None
        for i in range(r):
            if T[i][enter] > 0:
                ratio = T[i][ncol] / T[i][enter]
                if best is None or ratio < best[0] or (ratio == best[0] and basis[i] < basis[best[1]]): best = (ratio, i)
        if best is None: break       # unbounded (cannot happen: the objective is bounded by 0)
        i = best[1]; piv = T[i][enter]; T[i] = [x / piv for x in T[i]]
        for k in range(r):
            if k != i and T[k][enter] != 0:
                f = T[k][enter]; T[k] = [x - f * y for x, y in zip(T[k], T[i])]
        f = obj[enter]; obj = [x - f * y for x, y in zip(obj, T[i])]; basis[i] = enter
    return obj[ncol], T, basis, obj, art


def _value(T, basis, d):
    x = [F(0)] * d
    for i, bv in enumerate(basis):
        if bv < d: x[bv] = T[i][-1]
    return x


def realize(rows, d):
    """('ok', v) with v a strict integer point, or ('conflict', core)"""
    if not rows: return 'ok', [1 << (d + 1 + g) for g in range(d)]
    opt, T, basis, obj, art = _phase1(rows, d)
    if opt == 0:
        x = _value(T, basis, d); v = [xi + 1 for xi in x]
        den = 1
        for q in v: den = den * q.denominator // __import__('math').gcd(den, q.denominator)
        vi = [int(q * den) for q in v]; K = 1 << (d + 1)
        out = [K * x_ + (1 << g) for g, x_ in enumerate(vi)]
        assert all(sum(a[g] * out[g] for g in range(d)) > 0 for a in rows) and all(x_ > 0 for x_ in out)
        return 'ok', out
    # infeasible: dual values of the rows = reduced costs of their slack columns (sign: the slack enters with -1)
    r = len(rows)
    core = [j for j in range(r) if obj[d + j] != 0]
    if not core or realize_check([rows[j] for j in core], d): core = list(range(r))     # fall back to all rows
    return 'conflict', core


def realize_check(rows, d):
    """True iff the rows are realizable (no core extraction)"""
    if not rows: return True
    return _phase1(rows, d)[0] == 0


if __name__ == '__main__':
    import _paths, kcegar
    rng = random.Random(1); bad = 0; tot = 0
    for d in (2, 3, 4, 5):
        reps = kcegar.reps(d); P = [(S, T) for S in range(1, 1 << d) for T in range(S + 1, 1 << d) if S & T == 0]
        sv = lambda v, S: sum(v[g] for g in range(d) if S >> g & 1)
        for t in range(300):
            # a random set of comparisons with signs taken from a real type: must be realizable
            v = rng.choice(reps); v = [v[k] for k in rng.sample(range(d), d)]
            Q = rng.sample(P, min(len(P), rng.randint(1, 12)))
            rows = [[(1 if S >> g & 1 else 0) - (1 if T >> g & 1 else 0) for g in range(d)] for S, T in Q]
            rows = [a if sum(a[g] * v[g] for g in range(d)) > 0 else [-x for x in a] for a in rows]
            st, w = realize(rows, d); tot += 1; bad += st != 'ok'
            # flip one sign: realizable iff some type has those signs (decided by the type list)
            j = rng.randrange(len(rows)); rows2 = [list(a) for a in rows]; rows2[j] = [-x for x in rows2[j]]
            truth = False
            for rep in reps:
                for perm in itertools.permutations(range(d)):
                    u = [0] * d
                    for k in range(d): u[perm[k]] = rep[k]
                    if all(sum(a[g] * u[g] for g in range(d)) > 0 for a in rows2): truth = True; break
                if truth: break
            st2, w2 = realize(rows2, d); tot += 1
            if (st2 == 'ok') != truth: bad += 1; print('MISMATCH', d, rows2, st2, truth)
            if st2 == 'conflict' and realize_check([rows2[k] for k in w2], d): bad += 1; print('BAD CORE', d, rows2, w2)
    print('self-test: %d LP calls against the type lists, %d mismatches' % (tot, bad))
