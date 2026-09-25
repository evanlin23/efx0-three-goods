"""Independent model of LB4^r as defined in lean/EFX/LB4R.lean (PR #35) and lean/EFX/PreAllocK.lean.

A state is (base, pick, marked):
  base[g]  = agent holding g in its base, or -1 (junk)
  pick[i]  = good, or -1
  marked[i] = bool (upgraded or rotated)
Needs are derived (needsOf of LB4R.lean). Everything below transcribes the Lean definitions:
  phase1 / phase1State, UpEligible / UpStep / UpRun, rotate / FrozenAt / RotChecks / RotStep,
  Completion / OC / ownerNeeds / Output.
Two owner-needs conventions for the completion test:
  'bundle' : Lean's Output (owner's needs N_o^X = {g not in X_o : v_o(g) > v_o(X_o)})
  'base'   : the owner keeps needsOf (Valid.sound, the lb4.c -w0 variant)
"""
import itertools
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType


class Inst:
    def __init__(self, v):
        self.v = v
        self.n = len(v)
        self.m = len(v[0])
        self.R = [[g for g in range(self.m) if v[i][g] > 0] for i in range(self.n)]


# ---------------------------------------------------------------- needs, NA, frozen

def base_of(inst, s, i):
    base = s[0]
    return [g for g in range(inst.m) if base[g] == i]


def needs_of(inst, s, i):
    """needsOf of LB4R.lean."""
    base, pick, marked = s
    v = inst.v
    if marked[i]:
        vb = sum(v[i][g] for g in range(inst.m) if base[g] == i)
        return frozenset(g for g in range(inst.m) if base[g] != i and vb < v[i][g])
    y = pick[i]
    if y < 0:
        return frozenset(g for g in range(inst.m) if v[i][g] > 0)
    return frozenset(g for g in range(inst.m) if v[i][g] > 0 and v[i][y] < v[i][g])


def all_needs(inst, s):
    return [needs_of(inst, s, i) for i in range(inst.n)]


def NA_of(needs):
    out = set()
    for N in needs:
        out |= N
    return out


def frozen_pre(inst, s, NA):
    """PreAllocK.Frozen: base is one good, in NA (no marked condition)."""
    res = []
    for i in range(inst.n):
        B = base_of(inst, s, i)
        res.append(len(B) == 1 and B[0] in NA)
    return res


def frozen_at(inst, s, NA):
    """LB4R.FrozenAt: unmarked and Frozen."""
    fr = frozen_pre(inst, s, NA)
    return [fr[i] and not s[2][i] for i in range(inst.n)]


def omega(inst, s, needs=None):
    """omega = |J| - capSum; cap = 0 if frozen else 2 - |B_i| (signed)."""
    if needs is None:
        needs = all_needs(inst, s)
    NA = NA_of(needs)
    fr = frozen_pre(inst, s, NA)
    J = sum(1 for g in range(inst.m) if s[0][g] == -1)
    cs = sum(0 if fr[i] else 2 - len(base_of(inst, s, i)) for i in range(inst.n))
    return J - cs


# ---------------------------------------------------------------- Phase 1

def fav(inst, i, S):
    best = None
    for g in S:  # S in list order; first on ties
        if inst.v[i][g] > 0 and (best is None or inst.v[i][g] > inst.v[i][best]):
            best = g
    return best


def phase1_run(inst, tau):
    n, m, v = inst.n, inst.m, inst.v
    U = list(range(n))
    G0 = list(range(m))
    tau = list(tau)
    run = []
    while U:
        lost = [i for i in U if any(g not in G0 for g in inst.R[i])]
        if lost:
            def key(i):
                f = fav(inst, i, G0)
                r = len(inst.R[i]) if f is None else sum(1 for h in inst.R[i] if v[i][f] < v[i][h])
                return (r, sum(1 for g in G0 if v[i][g] > 0), i)
            x = min(lost, key=key)
        else:
            h = tau[0] if tau else 0
            x = U[h % len(U)]
            tau = tau[1:]
        f = fav(inst, x, G0)
        run.append((x, f, "P" if lost else "I"))
        U.remove(x)
        if f is not None:
            G0.remove(f)
    return run


def phase1_state(inst, tau=()):
    run = phase1_run(inst, tau)
    base = [-1] * inst.m
    pick = [-1] * inst.n
    for x, f, _ in run:
        if f is not None:
            base[f] = x
            pick[x] = f
    return (tuple(base), tuple(pick), tuple([False] * inst.n)), run


# ---------------------------------------------------------------- upgrades

def up_eligible(inst, s, pol, k, g, needs, NA):
    base, pick, marked = s
    v = inst.v
    if marked[k]:
        return False
    y = pick[k]
    if y < 0 or base_of(inst, s, k) != [y]:
        return False
    if y in NA:
        return False
    Nk = needs[k]
    if not Nk:
        return False
    if base[g] != -1 or not v[k][g] > 0:
        return False
    if not any(v[k][x] <= v[k][y] + v[k][g] for x in Nk):
        return False
    if pol == "shrink":
        return True
    if pol == "envyFree":
        return sum(v[k][h] for h in inst.R[k] if h != y and h != g) <= v[k][y] + v[k][g]
    return False  # none


def up_run(inst, s, pol):
    steps = []
    while True:
        needs = all_needs(inst, s)
        NA = NA_of(needs)
        cand = [(k, g) for k in range(inst.n) for g in range(inst.m) if up_eligible(inst, s, pol, k, g, needs, NA)]
        if not cand:
            return s, steps
        k = min(c[0] for c in cand)
        gs = [g for (kk, g) in cand if kk == k]
        g = max(gs, key=lambda h: (inst.v[k][h], -h))
        base, pick, marked = s
        base = list(base)
        base[g] = k
        marked = list(marked)
        marked[k] = True
        s = (tuple(base), pick, tuple(marked))
        steps.append((k, g))


# ---------------------------------------------------------------- rotations

def rotate(s, c, O):
    base, pick, marked = s
    k = c[0]
    pos = {a: idx for idx, a in enumerate(c)}
    nb = list(base)
    Oset = set(O)
    for g in range(len(base)):
        if g in Oset:
            nb[g] = k
        elif base[g] >= 0 and base[g] in pos:
            idx = pos[base[g]]
            nb[g] = c[idx + 1] if idx + 1 < len(c) else -1
    npk = list(pick)
    for x in c:
        idx = pos[x]
        npk[x] = -1 if idx == 0 else pick[c[idx - 1]]
    nm = list(marked)
    for x in c:
        nm[x] = (x == k)
    return (tuple(nb), tuple(npk), tuple(nm))


def rot_checks(inst, s):
    needs = all_needs(inst, s)
    NA = NA_of(needs)
    base, pick, marked = s
    # V1
    for g in range(inst.m):
        if base[g] == -1 and g in NA:
            return False
    bases = [base_of(inst, s, i) for i in range(inst.n)]
    # V2
    for i in range(inst.n):
        if len(bases[i]) >= 2 and any(g in NA for g in bases[i]):
            return False
    # marked agents: no base good in NA
    for i in range(inst.n):
        if marked[i] and any(g in NA for g in bases[i]):
            return False
    if sum(1 for i in range(inst.n) if len(bases[i]) >= 3) > 1:
        return False
    return True


def chains(inst, s, needs, NA):
    """All need chains of RotStep: distinct agents, >= 2, all but last FrozenAt with pick needed by next,
    last not FrozenAt."""
    fa = frozen_at(inst, s, NA)
    pick = s[1]
    out = []

    def ext(c):
        a = c[-1]
        y = pick[a]
        if y < 0:
            return
        for b in range(inst.n):
            if b in c or y not in needs[b]:
                continue
            if fa[b]:
                ext(c + [b])  # b must be a middle agent (frozen agents cannot end a chain)
            else:
                out.append(c + [b])  # b ends the chain (non-frozen agents cannot be middle)
    for k in range(inst.n):
        if fa[k]:
            ext([k])
    return out


def rot_steps(inst, s):
    """All successor states of one RotStep (as a set), plus a description for each."""
    needs = all_needs(inst, s)
    NA = NA_of(needs)
    res = {}
    for c in chains(inst, s, needs, NA):
        k, last = c[0], c[-1]
        pool = [g for g in range(inst.m) if inst.v[k][g] > 0 and (s[0][g] == -1 or s[0][g] == last)]
        for r in range(1, len(pool) + 1):
            for O in itertools.combinations(pool, r):
                s2 = rotate(s, c, O)
                if rot_checks(inst, s2):
                    if s2 not in res:
                        res[s2] = (tuple(c), O)
    return res


def reach(inst, s1, q):
    """Distinct states reachable from s1 with at most q rotations; returns list of dicts per depth of NEW
    states (depth = least number of rotations) with a parent pointer."""
    levels = [{s1: None}]
    seen = {s1}
    for d in range(1, q + 1):
        new = {}
        for s in levels[-1]:
            for s2, desc in rot_steps(inst, s).items():
                if s2 not in seen:
                    seen.add(s2)
                    new[s2] = (s, desc)
        levels.append(new)
    return levels


# ---------------------------------------------------------------- completion test: SAT

class Cnf:
    def __init__(self):
        self.nv = 0
        self.cl = []

    def new(self):
        self.nv += 1
        return self.nv


def build_model(inst, s, o, conv, needs=None):
    """The exact model of Output(s, o, .) as clauses plus cardinality constraints over boolean variables.
    Returns None if trivially infeasible, else (nv, clauses, cards, x, holders, J) with cards a list of
    (lits, op, bound), op in {'<=', '=='}; a 'dyn' agent's cap is expressed by clauses (F -> no junk) and an
    at-most-1 card."""
    n, m, v = inst.n, inst.m, inst.v
    if needs is None:
        needs = all_needs(inst, s)
    base = s[0]
    bases = [base_of(inst, s, i) for i in range(n)]
    J = [g for g in range(m) if base[g] == -1]
    om = omega(inst, s, needs)
    if all(len(b) <= 2 for b in bases):
        if (o is None) != (om <= 0):
            return None
    NA_all = NA_of(needs)
    for j in range(n):
        if j != o and len(bases[j]) >= 3:
            return None
    if o is not None:
        if len(bases[o]) == 1:
            y = bases[o][0]
            if any(y in needs[i] for i in range(n) if i != o):
                return None
    cnf = Cnf()
    cards = []
    status = {}
    for j in range(n):
        if j == o:
            continue
        B = bases[j]
        if len(B) == 1:
            y = B[0]
            if conv == "base" or o is None:
                fz = y in NA_all
                status[j] = ("frozen",) if fz else ("free", 1)
            else:
                others = any(y in needs[i] for i in range(n) if i != o)
                if others:
                    status[j] = ("frozen",)
                elif v[o][y] > 0:
                    status[j] = ("dyn", y)
                else:
                    status[j] = ("free", 1)
        else:
            status[j] = ("free", 2 - len(B))
    x = {}
    holders = {g: [] for g in J}
    for g in J:
        if o is not None:
            x[(g, o)] = cnf.new()
            holders[g].append(o)
        for j, st in status.items():
            if st[0] == "frozen" or (st[0] == "free" and st[1] <= 0):
                continue
            x[(g, j)] = cnf.new()
            holders[g].append(j)
    for g in J:
        lits = [x[(g, j)] for j in holders[g]]
        if not lits:
            return None
        cards.append((lits, "==", 1))
    for j, st in status.items():
        lits = [x[(g, j)] for g in J if (g, j) in x]
        if st[0] == "free" and st[1] > 0:
            if len(lits) > st[1]:
                cards.append((lits, "<=", st[1]))
        elif st[0] == "dyn":
            y = st[1]
            F = cnf.new()
            for l in lits:
                cnf.cl.append([-F, -l])
            if len(lits) > 1:
                cards.append((lits, "<=", 1))
            RoJ = [g for g in J if v[o][g] > 0]
            vBo = sum(v[o][g] for g in bases[o])
            for r in range(len(RoJ) + 1):
                for S in itertools.combinations(RoJ, r):
                    if vBo + sum(v[o][g] for g in S) < v[o][y]:
                        cnf.cl.append([x[(g, o)] for g in RoJ if g not in S] + [F])
    if o is not None:
        Bo = bases[o]
        for j in range(n):
            if j == o:
                continue
            RJ = [g for g in J if v[j][g] > 0]
            RB = [g for g in Bo if v[j][g] > 0]
            outside_base = any(v[j][g] == 0 for g in Bo)
            W = None
            if not outside_base:
                W = cnf.new()
                for g in J:
                    if v[j][g] == 0:
                        cnf.cl.append([-x[(g, o)], W])
            vBj = sum(v[j][g] for g in bases[j])
            canj = all((g, j) in x for g in RJ)
            for stat in itertools.product("WJO", repeat=len(RJ)):
                if not canj and "J" in stat:
                    continue
                Q = RB + [g for g, st in zip(RJ, stat) if st == "W"]
                P = [g for g, st in zip(RJ, stat) if st == "J"]
                Qv = sum(v[j][g] for g in Q)
                hold = vBj + sum(v[j][g] for g in P)
                viol_out = Qv > hold
                viol_in = bool(Q) and (Qv - min(v[j][g] for g in Q) > hold)
                if not viol_out:
                    continue
                clause = []
                for g, st in zip(RJ, stat):
                    if st == "W":
                        clause.append(-x[(g, o)])
                    elif st == "J":
                        clause.append(-x[(g, j)])
                    else:
                        clause.append(x[(g, o)])
                        if (g, j) in x:
                            clause.append(x[(g, j)])
                if viol_in or outside_base:
                    cnf.cl.append(clause)
                else:
                    cnf.cl.append(clause + [-W])
    return cnf.nv, cnf.cl, cards, x, holders, J


def _decode(s, model_true, x, holders, J):
    X = list(s[0])
    for g in J:
        for j in holders[g]:
            if x[(g, j)] in model_true:
                X[g] = j
    return X


def output_sat(inst, s, o, conv, needs=None, want_model=False, backend="sat"):
    """Exact test: is there X with Output(s, o, X) (conv='bundle': Lean's ownerNeeds; 'base': needsOf)?
    backend 'sat' (Glucose 3, cardinalities by pairwise / sequential counter) or 'milp' (HiGHS, cardinalities
    and clauses as linear rows). Returns (bool, X or None)."""
    M = build_model(inst, s, o, conv, needs)
    if M is None:
        return False, None
    nv, clauses, cards, x, holders, J = M
    if backend == "sat":
        cl = list(clauses)
        top = nv
        for lits, op, b in cards:
            if op == "==":
                cl.append(list(lits))
                for a, c in itertools.combinations(lits, 2):
                    cl.append([-a, -c])
            else:
                enc = CardEnc.atmost(lits=lits, bound=b, top_id=top, encoding=EncType.seqcounter)
                top = max(top, enc.nv)
                cl.extend(enc.clauses)
        with Solver(name="g3", bootstrap_with=cl) as S:
            if not S.solve():
                return False, None
            if not want_model:
                return True, None
            mt = set(l for l in S.get_model() if l > 0)
        return True, _decode(s, mt, x, holders, J)
    # MILP
    import numpy as np
    from scipy.optimize import milp, LinearConstraint, Bounds
    from scipy.sparse import lil_matrix
    if any(len(c) == 0 for c in clauses):
        return False, None
    nv = nv + 1  # a dummy variable so that the model is never empty
    rows = len(clauses) + len(cards)
    A = lil_matrix((max(rows, 1), nv))
    lb = np.full(max(rows, 1), -np.inf)
    ub = np.full(max(rows, 1), np.inf)
    r = 0
    for c in clauses:  # sum(pos) - sum(neg) >= 1 - #neg
        neg = 0
        for l in c:
            if l > 0:
                A[r, l - 1] += 1
            else:
                A[r, -l - 1] -= 1
                neg += 1
        lb[r] = 1 - neg
        r += 1
    for lits, op, b in cards:
        for l in lits:
            A[r, l - 1] += 1
        ub[r] = b
        if op == "==":
            lb[r] = b
        r += 1
    res = milp(c=np.zeros(nv), constraints=[LinearConstraint(A.tocsr(), lb, ub)],
               integrality=np.ones(nv), bounds=Bounds(0, 1), options={"presolve": True})
    if res.status == 2:  # infeasible
        return False, None
    if res.status != 0:
        raise RuntimeError(f"milp status {res.status}: {res.message}")
    if not want_model:
        return True, None
    mt = set(i + 1 for i in range(nv) if res.x[i] > 0.5)
    return True, _decode(s, mt, x, holders, J)


def output_check(inst, s, o, X, conv, needs=None):
    """Literal check of Output(s, o, X) (conv='bundle') or the base-needs variant, by the raw definitions."""
    n, m, v = inst.n, inst.m, inst.v
    if needs is None:
        needs = all_needs(inst, s)
    base = s[0]
    bases = [base_of(inst, s, i) for i in range(n)]
    bund = [[g for g in range(m) if X[g] == i] for i in range(n)]
    # ownerNeeds
    N2 = list(needs)
    if o is not None and conv == "bundle":
        vo = sum(v[o][g] for g in bund[o])
        N2[o] = frozenset(g for g in range(m) if X[g] != o and vo < v[o][g])
    NA2 = NA_of(N2)
    fr = [len(bases[i]) == 1 and bases[i][0] in NA2 for i in range(n)]
    # Completion
    if any(not (0 <= X[g] < n) for g in range(m)):
        return False
    if any(base[g] >= 0 and X[g] != base[g] for g in range(m)):
        return False
    if o is not None and fr[o]:
        return False
    for j in range(n):
        if j == o:
            continue
        cj = [g for g in bund[j] if base[g] == -1]
        if fr[j] and cj:
            return False
        if not fr[j] and len(cj) + len(bases[j]) > 2:
            return False
    # OC
    if o is not None:
        for j in range(n):
            if j == o:
                continue
            vj = sum(v[j][g] for g in bund[j])
            for h in bund[o]:
                if sum(v[j][g] for g in bund[o] if g != h) > vj:
                    return False
    if all(len(b) <= 2 for b in bases):
        if (o is None) != (omega(inst, s, needs) <= 0):
            return False
    return True


def output_brute(inst, s, o, conv):
    """Plain brute force: every map from the junk to the agents."""
    J = [g for g in range(inst.m) if s[0][g] == -1]
    needs = all_needs(inst, s)
    X = list(s[0])
    for assign in itertools.product(range(inst.n), repeat=len(J)):
        for g, a in zip(J, assign):
            X[g] = a
        if output_check(inst, s, o, X, conv, needs):
            return True
    return False


def any_output(inst, s, conv, owners=None):
    """Some owner (or none) with an output. Returns list of owners (None = no owner) that work."""
    needs = all_needs(inst, s)
    cand = [None] + list(range(inst.n)) if owners is None else owners
    good = []
    for o in cand:
        ok, _ = output_sat(inst, s, o, conv, needs)
        if ok:
            good.append(o)
    return good
