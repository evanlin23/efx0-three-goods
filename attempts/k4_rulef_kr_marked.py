#!/usr/bin/env python3
"""Lemma KR (k4/rulef.md §3) without "every marked agent's base avoids NA": the rotation need not be a RotStep.

Written from the Lean definitions of lean/EFX/LB4R.lean (needsOf, Frozen, FrozenAt, Valid, Inv, rotate, RotChecks,
RotStep) and lean/EFX/K4C4AB.lean (Wl, Threatened), for one instance: three agents k = 0, o = 1, m = 2 and four goods
y = 0, g = 1, j1 = 2, j2 = 3. It checks that the state satisfies Inv and every hypothesis of Lemma KR as the text states
it (bases of at most two goods, o not frozen with |B_o| <= 1, the empty service of E = {} , the chain [k, o], the base
O = [j1, j2], (i), (ii), o not threatened after the rotation so eps = 0, (iii) by Inv), that the deficit bound of the
conclusion holds, and that RotChecks fails on the rotated state (the marked agent m keeps a one-good base that o needs
after the rotation), so the rotation is not a RotStep. Exit status 0 iff all of this holds.
"""
import sys

AGENTS = [0, 1, 2]
GOODS = [0, 1, 2, 3]
K, O_, M = 0, 1, 2
V = {K: [3, 0, 2, 2], O_: [1, 2, 0, 0], M: [0, 5, 0, 0]}


def value(i, S):
    return sum(V[i][g] for g in S)


class State:
    def __init__(self, base, pick, marked):
        self.base, self.pick, self.marked = base, pick, marked  # dict good -> agent/None, agent -> good/None, set


def base_of(s, i):
    return [g for g in GOODS if s.base[g] == i]


def junk(s):
    return [g for g in GOODS if s.base[g] is None]


def needs_of(s, i, g):  # EFX.LB4R.needsOf
    if i in s.marked:
        return s.base[g] != i and value(i, base_of(s, i)) < V[i][g]
    y = s.pick[i]
    return 0 < V[i][g] and (y is None or V[i][y] < V[i][g])


def NA(s, g):
    return any(needs_of(s, i, g) for i in AGENTS)


def frozen(s, j):  # EFX.LB4.Frozen
    B = base_of(s, j)
    return len(B) == 1 and NA(s, B[0])


def frozen_at(s, j):
    return j not in s.marked and frozen(s, j)


def valid(s):
    return (all(not NA(s, g) for g in junk(s)) and
            all(not NA(s, g) for i in AGENTS if len(base_of(s, i)) >= 2 for g in base_of(s, i)))


def inv(s):
    return (valid(s) and
            all(base_of(s, i) == ([] if s.pick[i] is None else [s.pick[i]]) for i in AGENTS if i not in s.marked) and
            all(V[i][s.pick[i]] > 0 for i in AGENTS if i not in s.marked and s.pick[i] is not None))


def rotate(s, c, O):  # EFX.LB4R.rotate
    base = {}
    for g in GOODS:
        if g in O:
            base[g] = c[0]
        elif s.base[g] is None:
            base[g] = None
        elif s.base[g] in c:
            idx = c.index(s.base[g]) + 1
            base[g] = c[idx] if idx < len(c) else None
        else:
            base[g] = s.base[g]
    pick = {}
    for x in AGENTS:
        if x in c:
            pick[x] = None if c.index(x) == 0 else s.pick[c[c.index(x) - 1]]
        else:
            pick[x] = s.pick[x]
    marked = {x for x in AGENTS if x == c[0] or (x in s.marked and x not in c)}
    return State(base, pick, marked)


def rot_checks(s):  # EFX.LB4R.RotChecks
    big = [i for i in AGENTS if len(base_of(s, i)) >= 3]
    return (valid(s) and
            all(not NA(s, g) for i in AGENTS if i in s.marked for g in base_of(s, i)) and len(big) <= 1)


def W(s, r):  # EFX.LB4R.Wl
    return [g for g in GOODS if s.base[g] is None or s.base[g] == r]


def threatened(x, L, H):  # EFX.LB4R.Threatened
    return any(value(x, H) < value(x, [g for g in L if g != h]) for h in L)


def in_E(s, o, x):
    return x != o and threatened(x, W(s, o), base_of(s, x))


def other_slots(s, w):
    return sum(0 if (j == w or frozen(s, j)) else 2 - len(base_of(s, j)) for j in AGENTS)


def main():
    s = State(base={0: K, 1: M, 2: None, 3: None}, pick={K: 0, O_: None, M: None}, marked={M})
    c, O = [K, O_], [2, 3]
    checks = []
    checks.append(("Inv", inv(s)))
    checks.append(("bases have at most two goods", all(len(base_of(s, i)) <= 2 for i in AGENTS)))
    checks.append(("o is not frozen, |B_o| <= 1", not frozen(s, O_) and len(base_of(s, O_)) <= 1))
    E = [x for x in AGENTS if in_E(s, O_, x)]
    checks.append(("E is empty (the empty service is a ∅-service, size 0)", E == []))
    checks.append(("chain [k, o]: k frozen, its pick needed by o", frozen_at(s, K) and needs_of(s, O_, s.pick[K])))
    checks.append(("o is not FrozenAt", not frozen_at(s, O_)))
    checks.append(("O ⊆ R_k ∩ W, v_k(O) > v_k(Y_k)", all(V[K][g] > 0 and g in W(s, O_) for g in O)
                   and value(K, O) > V[K][s.pick[K]]))
    t = rotate(s, c, O)
    checks.append(("(ii) o is not frozen after the rotation", not frozen(t, O_)))
    checks.append(("o is not threatened after the rotation (eps = 0)", not in_E(t, K, O_)))
    kappa = other_slots(s, O_)
    E2 = [x for x in AGENTS if in_E(t, K, x)]
    deficit_after = 0 - other_slots(t, K)
    checks.append(("deficit after <= |σ| - κ - 1 - c_k + eps", E2 == [] and deficit_after <= 0 - kappa - 1 - 0 + 0))
    checks.append(("the marked agent m holds a one-good base needed by o after the rotation",
                   M in t.marked and base_of(t, M) == [1] and needs_of(t, O_, 1)))
    checks.append(("RotChecks fails on the rotated state (not a RotStep)", not rot_checks(t)))
    ok = True
    for name, val in checks:
        print(("ok   " if val else "FAIL ") + name)
        ok = ok and val
    print("kappa =", kappa, " deficit after =", deficit_after, " NA after =", [g for g in GOODS if NA(t, g)])
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
