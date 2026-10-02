"""An independent model of LB4r with at most one rotation, and the checks of Propositions Q and HH (k4/lemmam_bt.md)
with it. Written independently by the referee of PR #83 (the review of workstream proof/k4-lemmam-bt), from
lean/EFX/LB4R.lean and lean/EFX/PreAllocK.lean (phase1/nextAgent/key, UpEligible/UpStep/UpRun,
rotate/FrozenAt/RotChecks/RotStep, Completion/OC/ownerNeeds/Output) and from the prose of k4/c4.md §7 and
k4/lemmam_bt.md §2-§3. It shares no code with k4/c4_verify_H/lb4r.py, k4/lemmam_bt.py or k4/lemmam_bt_hh.py: the
instances are built again here, and the Output test is a MILP (scipy/HiGHS) with big-M rows, one per agent j != o and
per good h that could be removed from X_o, not lb4r.py's clause enumeration. lb4r.py is imported only to compare with
(validation, and the model A option of the driver).

The referee's scratch files (mine.py: class Model and efx0_raw; inst.py: the builders and check_core; exact_run.py,
d2_check.py, validate_mine.py: the drivers) are put together here with their code unchanged except for imports, paths
and the entry points. The logs results/k4_lemmam_bt/indep_*.log were made by those scratch files (the same code):
  python3 k4/lemmam_bt_indep.py exact HH3 --model=R --conv=bundle,base [--log=FILE]   every first agent: an Output
                                     with at most one rotation? (indep_exactR_HH3.log; Hq3: indep_exactR_Hq3.log;
                                     HH2 with --conv=bundle: indep_exactR_HH2.log, where outputs exist: t >= 3 is sharp)
  python3 k4/lemmam_bt_indep.py d2                    K4.D on HH_3 and HH_4: (x^A_12, x^B_12, then index order) has an
                                                      Output without rotation (indep_d2.log)
  python3 k4/lemmam_bt_indep.py validate SEED R [skipH]   this model against lb4r.py on H_1, H_2 and R random small
                                                      instances (indep_validate_random.log: 7 120 skipH)
  python3 k4/lemmam_bt_indep.py core                  the instances are connected k = 4 cores with strict profiles
Names in the logs: lA, lB, x{j}{i}A, y{j}A, ... (agents), as built by build_HH / build_Hq below. One worker."""
import itertools, os, random, sys, time
import networkx as nx
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'c4_verify_H'))
import lb4r as M

# ----------------------------------------------------------------------------------------------------------------
# the model (mine.py)
class Model:
    def __init__(self, v):
        self.v = v
        self.n = len(v)
        self.m = len(v[0])
        self.R = [frozenset(g for g in range(self.m) if v[i][g] > 0) for i in range(self.n)]

    # ---------------------------------------------------------------- needs
    def baseof(self, st, i):
        return [g for g in range(self.m) if st["base"][g] == i]

    def needs(self, st, i):
        v = self.v[i]
        if i in st["marked"]:
            vb = sum(v[g] for g in self.baseof(st, i))
            return frozenset(g for g in range(self.m) if st["base"][g] != i and v[g] > vb)
        y = st["pick"][i]
        if y is None:
            return frozenset(self.R[i])
        return frozenset(g for g in self.R[i] if v[g] > v[y])

    def NA(self, N):
        out = set()
        for x in N:
            out |= x
        return out

    def frozen(self, st, i, NA):
        B = self.baseof(st, i)
        return len(B) == 1 and B[0] in NA

    def omega(self, st):
        N = [self.needs(st, i) for i in range(self.n)]
        NA = self.NA(N)
        J = sum(1 for g in range(self.m) if st["base"][g] is None)
        S = sum(0 if self.frozen(st, i, NA) else 2 - len(self.baseof(st, i)) for i in range(self.n))
        return J - S

    # ---------------------------------------------------------------- Phase 1 (Lean's phase1 with tau)
    def phase1(self, tau):
        n, v = self.n, self.v
        U = list(range(n))
        G0 = set(range(self.m))
        tau = list(tau)
        pick = [None] * n
        order = []
        while U:
            lost = [i for i in U if not self.R[i] <= G0]
            if lost:
                def key(i):
                    avail = [g for g in self.R[i] if g in G0]
                    if avail:
                        f = max(avail, key=lambda g: v[i][g])
                        r = sum(1 for h in self.R[i] if v[i][h] > v[i][f])
                    else:
                        r = len(self.R[i])
                    return (r, len(avail), i)
                x = min(lost, key=key)
                kind = "P"
            else:
                h = tau.pop(0) if tau else 0
                x = U[h % len(U)]
                kind = "I"
            avail = [g for g in self.R[x] if g in G0]
            f = max(avail, key=lambda g: v[x][g]) if avail else None
            pick[x] = f
            if f is not None:
                G0.discard(f)
            U.remove(x)
            order.append((x, f, kind))
        base = [None] * self.m
        for i, f in enumerate(pick):
            if f is not None:
                base[f] = i
        return {"base": tuple(base), "pick": tuple(pick), "marked": frozenset()}, order

    # ---------------------------------------------------------------- upgrades
    def up_eligible(self, st, pol, k, g, N, NA):
        if pol == "none" or k in st["marked"]:
            return False
        y = st["pick"][k]
        if y is None or self.baseof(st, k) != [y] or y in NA or not N[k]:
            return False
        if st["base"][g] is not None or self.v[k][g] <= 0:
            return False
        vk = self.v[k]
        if not any(vk[x] <= vk[y] + vk[g] for x in N[k]):
            return False
        if pol == "envyFree":
            return sum(vk[h] for h in self.R[k] if h != y and h != g) <= vk[y] + vk[g]
        return True

    def uprun(self, st, pol):
        steps = []
        while True:
            N = [self.needs(st, i) for i in range(self.n)]
            NA = self.NA(N)
            el = [(k, g) for k in range(self.n) for g in range(self.m) if self.up_eligible(st, pol, k, g, N, NA)]
            if not el:
                return st, steps
            k = min(e[0] for e in el)
            g = max((gg for kk, gg in el if kk == k), key=lambda h: (self.v[k][h], -h))
            base = list(st["base"]); base[g] = k
            st = {"base": tuple(base), "pick": st["pick"], "marked": st["marked"] | {k}}
            steps.append((k, g))

    # ---------------------------------------------------------------- rotations
    def rotate(self, st, c, O):
        pos = {a: t for t, a in enumerate(c)}
        base = []
        for g in range(self.m):
            if g in O:
                base.append(c[0])
            else:
                a = st["base"][g]
                if a is not None and a in pos:
                    base.append(c[pos[a] + 1] if pos[a] + 1 < len(c) else None)
                else:
                    base.append(a)
        pick = list(st["pick"])
        for t, a in enumerate(c):
            pick[a] = None if t == 0 else st["pick"][c[t - 1]]
        marked = (st["marked"] - set(c)) | {c[0]}
        return {"base": tuple(base), "pick": tuple(pick), "marked": frozenset(marked)}

    def rotchecks(self, st):
        N = [self.needs(st, i) for i in range(self.n)]
        NA = self.NA(N)
        for g in range(self.m):
            if st["base"][g] is None and g in NA:
                return False
        big = 0
        for i in range(self.n):
            B = self.baseof(st, i)
            if len(B) >= 2 and any(g in NA for g in B):
                return False
            if i in st["marked"] and any(g in NA for g in B):
                return False
            big += len(B) >= 3
        return big <= 1

    def rotsteps(self, st):
        N = [self.needs(st, i) for i in range(self.n)]
        NA = self.NA(N)
        frozenat = [i not in st["marked"] and self.frozen(st, i, NA) for i in range(self.n)]
        chains = []

        def grow(c):
            y = st["pick"][c[-1]]
            if y is None:
                return
            for b in range(self.n):
                if b in c or y not in N[b]:
                    continue
                if frozenat[b]:
                    grow(c + [b])
                else:
                    chains.append(c + [b])
        for k in range(self.n):
            if frozenat[k]:
                grow([k])
        out = {}
        for c in chains:
            k, last = c[0], c[-1]
            pool = [g for g in sorted(self.R[k]) if st["base"][g] is None or st["base"][g] == last]
            for r in range(1, len(pool) + 1):
                for O in itertools.combinations(pool, r):
                    s2 = self.rotate(st, c, set(O))
                    if self.rotchecks(s2):
                        key = (s2["base"], s2["pick"], s2["marked"])
                        out.setdefault(key, (s2, tuple(c), O))
        return list(out.values())

    # ---------------------------------------------------------------- Output, as a MILP
    def output(self, st, o, conv="bundle"):
        """Is there X with Output(st, o, X)? Returns (bool, X). conv='base': owner keeps the state's needs."""
        n, m, v = self.n, self.m, self.v
        N = [self.needs(st, i) for i in range(n)]
        bases = [self.baseof(st, i) for i in range(n)]
        J = [g for g in range(m) if st["base"][g] is None]
        if all(len(B) <= 2 for B in bases):
            if (o is None) != (self.omega(st) <= 0):
                return False, None
        if any(len(bases[j]) >= 3 and j != o for j in range(n)):
            return False, None
        others_need = lambda y, excl: any(y in N[i] for i in range(n) if i != excl)
        if o is not None and len(bases[o]) == 1:
            y = bases[o][0]
            # owner must not be Frozen under ownerNeeds: y is in X_o, so N_o^X never contains it
            if others_need(y, o) or (conv == "base" and y in N[o]):
                return False, None
        if o is None:
            NAs = self.NA(N)
        # variables
        idx = {}
        def var(name):
            if name not in idx:
                idx[name] = len(idx)
            return idx[name]
        status = {}
        for j in range(n):
            if j == o:
                continue
            B = bases[j]
            if len(B) == 1:
                y = B[0]
                if o is None:
                    status[j] = "frozen" if y in NAs else "free"
                elif others_need(y, o) or (conv == "base" and y in N[o]):
                    status[j] = "frozen"
                elif conv == "bundle" and v[o][y] > 0:
                    status[j] = "cond"     # frozen iff v_o(X_o) < v_o(y)
                else:
                    status[j] = "free"
            else:
                status[j] = "free"
        holders = {g: [] for g in J}
        for g in J:
            if o is not None:
                holders[g].append(o)
            for j, s_ in status.items():
                if s_ != "frozen" and 2 - len(bases[j]) > 0:
                    holders[g].append(j)
            if not holders[g]:
                return False, None
            for j in holders[g]:
                var(("x", g, j))
        rows = []  # (dict var->coef, lo, hi)
        for g in J:
            rows.append(({idx[("x", g, j)]: 1 for j in holders[g]}, 1, 1))
        for j, s_ in status.items():
            cap = 2 - len(bases[j])
            xs = [idx[("x", g, j)] for g in J if ("x", g, j) in idx]
            if not xs:
                continue
            if s_ == "cond":
                f = var(("f", j))
                y = bases[j][0]
                # at most cap goods, none if frozen: sum x + cap*f <= cap
                d = {x: 1 for x in xs}; d[f] = cap
                rows.append((d, -np.inf, cap))
                # if not frozen (f = 0) then v_o(X_o) >= v_o(y): v_o(B_o) + sum v_o(g) x[g,o] + BIG f >= v_o(y)
                BIG = v[o][y] + 1
                d = {idx[("x", g, o)]: v[o][g] for g in J if v[o][g] > 0}
                d[f] = d.get(f, 0) + BIG
                rows.append((d, v[o][y] - sum(v[o][g] for g in bases[o]), np.inf))
            else:
                rows.append(({x: 1 for x in xs}, -np.inf, cap))
        if o is not None:
            Bo = bases[o]
            for j in range(n):
                if j == o:
                    continue
                vj = v[j]
                # v_j(X_o) = const + sum over junk relevant to j
                cst = sum(vj[g] for g in Bo)
                lhs = {idx[("x", g, o)]: vj[g] for g in J if vj[g] > 0}
                # v_j(X_j) = v_j(B_j) + sum over junk in j's bundle
                hold = {idx[("x", g, j)]: vj[g] for g in J if vj[g] > 0 and ("x", g, j) in idx}
                hb = sum(vj[g] for g in bases[j])
                BIG = sum(vj[g] for g in range(m)) + 1
                # removal of a good outside R_j present in X_o: then v_j(X_o) <= v_j(X_j)
                outside_base = any(vj[g] == 0 for g in Bo)
                outside_junk = [g for g in J if vj[g] == 0]
                def add(rem_val, trigger_vars, always):
                    # cst + lhs - rem_val - hold <= hb  (+ BIG*(1 - trigger) when not always)
                    d = dict(lhs)
                    for k_, c_ in hold.items():
                        d[k_] = d.get(k_, 0) - c_
                    if always:
                        rows.append((d, -np.inf, hb - cst + rem_val))
                    else:
                        for t in trigger_vars:
                            d2 = dict(d); d2[t] = d2.get(t, 0) + BIG
                            rows.append((d2, -np.inf, hb - cst + rem_val + BIG))
                if outside_base:
                    add(0, [], True)
                elif outside_junk:
                    add(0, [idx[("x", g, o)] for g in outside_junk], False)
                for h in Bo:
                    if vj[h] > 0:
                        add(vj[h], [], True)
                for h in J:
                    if vj[h] > 0:
                        add(vj[h], [idx[("x", h, o)]], False)
        nv = len(idx) + 1
        A = lil_matrix((max(len(rows), 1), nv))
        lo = np.full(max(len(rows), 1), -np.inf); hi = np.full(max(len(rows), 1), np.inf)
        for r, (d, a, b) in enumerate(rows):
            for k_, c_ in d.items():
                A[r, k_] += c_
            lo[r] = a; hi[r] = b
        res = milp(c=np.zeros(nv), constraints=[LinearConstraint(A.tocsr(), lo, hi)], integrality=np.ones(nv),
                   bounds=Bounds(0, 1))
        if res.status == 2:
            return False, None
        if res.status != 0:
            raise RuntimeError(res.message)
        X = list(st["base"])
        for (kind, *rest), k_ in idx.items():
            if kind == "x" and res.x[k_] > 0.5:
                g, j = rest
                X[g] = j
        return True, X

    # ---------------------------------------------------------------- literal checks
    def output_literal(self, st, o, X, conv="bundle"):
        n, m, v = self.n, self.m, self.v
        N = [self.needs(st, i) for i in range(n)]
        bund = [[g for g in range(m) if X[g] == i] for i in range(n)]
        if o is not None and conv == "bundle":
            vo = sum(v[o][g] for g in bund[o])
            N[o] = frozenset(g for g in range(m) if X[g] != o and v[o][g] > vo)
        NA = self.NA(N)
        bases = [self.baseof(st, i) for i in range(n)]
        fr = [len(bases[i]) == 1 and bases[i][0] in NA for i in range(n)]
        for g in range(m):
            if X[g] is None or not (0 <= X[g] < n):
                return False, "unallocated"
            if st["base"][g] is not None and X[g] != st["base"][g]:
                return False, "base moved"
        if o is not None and fr[o]:
            return False, "owner frozen"
        for j in range(n):
            if j == o:
                continue
            junk = [g for g in bund[j] if st["base"][g] is None]
            if fr[j] and junk:
                return False, "frozen gets junk"
            if not fr[j] and len(junk) + len(bases[j]) > 2:
                return False, "cap"
        if o is not None:
            for j in range(n):
                if j == o:
                    continue
                vj = sum(v[j][g] for g in bund[j])
                for h in bund[o]:
                    if sum(v[j][g] for g in bund[o] if g != h) > vj:
                        return False, "OC"
        if all(len(B) <= 2 for B in bases) and (o is None) != (self.omega(st) <= 0):
            return False, "omega"
        return True, "ok"


def efx0_raw(v, X):
    """Raw EFX0: for all i != j and every h in X_j, v_i(X_i) >= v_i(X_j - h). Returns (ok, max bundle size)."""
    n, m = len(v), len(v[0])
    bund = [[g for g in range(m) if X[g] == i] for i in range(n)]
    for i in range(n):
        vi = sum(v[i][g] for g in bund[i])
        for j in range(n):
            if i == j:
                continue
            tot = sum(v[i][g] for g in bund[j])
            for h in bund[j]:
                if tot - v[i][h] > vi:
                    return False, None
    big = sum(1 for b in bund if len(b) > 2)
    return True, big


# ----------------------------------------------------------------------------------------------------------------
# the instances (inst.py)
def copy_H(t, tag, shared_u=None):
    """One copy of H_t with goods/agents suffixed by tag. Returns agents (list of (name, {good: value}))
    in H_t index order and goods list."""
    goods = []
    def G(nm):
        nm = nm + tag
        if nm not in goods:
            goods.append(nm)
        return nm
    gs = [G(f"g{j}") for j in range(1, t + 1)]
    z = G("z"); u = shared_u if shared_u is not None else G("u"); up = G("u'")
    if shared_u is not None and shared_u not in goods:
        pass
    agents = []
    agents.append(("l" + tag, {gs[0]: 8, z: 6, u: 5, up: 4}))
    for j in range(1, t + 1):
        e = gs[j] if j < t else z
        aa = []
        for i in range(1, 4):
            a = G(f"a{j}{i}"); b = G(f"b{j}{i}"); c = G(f"c{j}{i}")
            aa.append(a)
            agents.append((f"x{j}{i}" + tag, {a: 8, b: 6, c: 4, gs[j - 1]: 3}))
        agents.append((f"y{j}" + tag, {aa[0]: 8, aa[1]: 6, aa[2]: 4, e: 3}))
    return agents, goods


def to_matrix(agents, goods):
    gi = {g: k for k, g in enumerate(goods)}
    v = [[0] * len(goods) for _ in agents]
    for i, (_, d) in enumerate(agents):
        for g, val in d.items():
            v[i][gi[g]] = val
    return [a for a, _ in agents], list(goods), v


def build_H(t):
    ag, gd = copy_H(t, "")
    return to_matrix(ag, gd)


def build_Hq(t):
    ag, gd = copy_H(t, "")
    gd = gd + ["p"]
    ag = ag + [("q", {"p": 8, "b11": 4, "c11": 3, "u": 2})]
    return to_matrix(ag, gd)


def build_HH(t):
    agA, gdA = copy_H(t, "A")
    agB, gdB = copy_H(t, "B", shared_u="uA")
    goods = gdA + [g for g in gdB if g not in gdA]
    # index order: l_A, l_B, A's gadget agents, B's gadget agents
    agents = [agA[0], agB[0]] + agA[1:] + agB[1:]
    return to_matrix(agents, goods)


def check_core(names, goods, v):
    """Connected k = 4 core with a strict profile, checked from the definitions of k4/SCOUT.md s2:
    3 or 4 relevant goods; strictly balanced (top < sum of the others); private goods: <= 1 for 3-good agents,
    <= 2 for 4-good agents and then p + q < s + t; every good relevant to someone; connected;
    strict type: distinct values and no two disjoint nonempty subsets of R_i with equal sum."""
    n, m = len(v), len(v[0])
    R = [[g for g in range(m) if v[i][g] > 0] for i in range(n)]
    deg = [sum(1 for i in range(n) if v[i][g] > 0) for g in range(m)]
    msgs = []
    ok = True
    for i in range(n):
        vals = sorted((v[i][g] for g in R[i]), reverse=True)
        if len(R[i]) not in (3, 4):
            ok = False; msgs.append(f"{names[i]}: |R| = {len(R[i])}")
        if not vals[0] < sum(vals[1:]):
            ok = False; msgs.append(f"{names[i]}: not strictly balanced")
        priv = [g for g in R[i] if deg[g] == 1]
        shared = [g for g in R[i] if deg[g] > 1]
        if len(R[i]) == 3 and len(priv) > 1:
            ok = False; msgs.append(f"{names[i]}: 3-good with {len(priv)} private")
        if len(R[i]) == 4:
            if len(priv) > 2:
                ok = False; msgs.append(f"{names[i]}: {len(priv)} private")
            if len(priv) == 2 and not sum(v[i][g] for g in priv) < sum(v[i][g] for g in shared):
                ok = False; msgs.append(f"{names[i]}: p + q >= s + t")
        # strict type: all subset sums of disjoint subsets distinct
        sums = {}
        for r in range(1, len(R[i]) + 1):
            for S in itertools.combinations(R[i], r):
                sums[frozenset(S)] = sum(v[i][g] for g in S)
        for S1, S2 in itertools.combinations(sums, 2):
            if not (S1 & S2) and sums[S1] == sums[S2]:
                ok = False; msgs.append(f"{names[i]}: tie {sorted(S1)} {sorted(S2)}"); break
    if any(d == 0 for d in deg):
        ok = False; msgs.append("a good valued by nobody")
    Gr = nx.Graph()
    Gr.add_nodes_from([("a", i) for i in range(n)] + [("g", g) for g in range(m)])
    Gr.add_edges_from((("a", i), ("g", g)) for i in range(n) for g in R[i])
    conn = nx.is_connected(Gr)
    if not conn:
        ok = False; msgs.append("not connected")
    bigtop = [names[i] for i in range(n) if len(R[i]) == 4 and
              sorted((v[i][g] for g in R[i]), reverse=True)[0] > sum(sorted((v[i][g] for g in R[i]), reverse=True)[1:3])]
    n4 = sum(1 for i in range(n) if len(R[i]) == 4)
    return ok, msgs, bigtop, n4


# ----------------------------------------------------------------------------------------------------------------
# the driver (exact_run.py)
POLS = ["shrink", "envyFree", "none"]
BUILD = {"HH3": lambda: build_HH(3), "HH4": lambda: build_HH(4), "Hq3": lambda: build_Hq(3),
         "H3": lambda: build_H(3), "Hq2": lambda: build_Hq(2), "HH2": lambda: build_HH(2)}


def lb_to_my(s):
    base, pick, marked = s
    return {"base": tuple(None if b < 0 else b for b in base), "pick": tuple(None if p < 0 else p for p in pick),
            "marked": frozenset(i for i, x in enumerate(marked) if x)}


def my_to_lb(st):
    return (tuple(-1 if b is None else b for b in st["base"]), tuple(-1 if p is None else p for p in st["pick"]),
            tuple(i in st["marked"] for i in range(len(st["pick"]))))


def states_A(inst, a):
    s0, _ = M.phase1_state(inst, [a])
    out = {}
    for pol in POLS:
        s1, _ = M.up_run(inst, s0, pol)
        out.setdefault(s1, []).append((pol, 0, None))
        for s2, desc in M.rot_steps(inst, s1).items():
            out.setdefault(s2, []).append((pol, 1, desc))
    return out


def states_R(my, a):
    s0, _ = my.phase1([a])
    out = {}
    for pol in POLS:
        s1, _ = my.uprun(s0, pol)
        out.setdefault(my_to_lb(s1), []).append((pol, 0, None))
        for s2, c, O in my.rotsteps(s1):
            out.setdefault(my_to_lb(s2), []).append((pol, 1, (c, O)))
    return out


def exact_main(argv):
    args = [x for x in argv if not x.startswith("--")]
    opts = dict(x[2:].split("=", 1) for x in argv if x.startswith("--"))
    name = args[0]
    names, goods, v = BUILD[name]()
    inst = M.Inst(v); my = Model(v)
    model = opts.get("model", "A")
    convs = opts.get("conv", "bundle").split(",")
    agents = list(range(inst.n)) if len(args) < 2 else [names.index(x) for x in args[1].split(",")]
    logf = opts.get("log")
    done = set()
    if logf and os.path.exists(logf):
        for line in open(logf):
            if line.startswith("a=") and f"model={model}" in line:
                done.add(line.split()[0][2:])
    log = open(logf, "a") if logf else None

    def out(s):
        print(s, flush=True)
        if log:
            log.write(s + "\n"); log.flush()

    out(f"# {name}: n = {inst.n}, m = {inst.m}; model {model}; convs {convs}; first agents "
        f"{[names[a] for a in agents if names[a] not in done]}")
    T0 = time.time()
    for a in agents:
        if names[a] in done:
            continue
        t0 = time.time()
        sts = states_A(inst, a) if model == "A" else states_R(my, a)
        found = []
        tests = 0
        for s, tags in sts.items():
            needs = M.all_needs(inst, s)
            for conv in convs:
                for o in [None] + list(range(inst.n)):
                    tests += 1
                    if model == "A":
                        ok, X = M.output_sat(inst, s, o, conv, needs, want_model=True, backend="milp")
                    else:
                        ok, X = my.output(lb_to_my(s), o, conv)
                    if ok:
                        l1 = M.output_check(inst, s, o, X, conv, needs)
                        l2, _ = my.output_literal(lb_to_my(s), o, X, conv)
                        e, big = efx0_raw(v, X)
                        found.append((conv, o, tags, l1, l2, e, big))
        d0 = sum(1 for tags in sts.values() if any(t[1] == 0 for t in tags))
        out(f"a={names[a]} idx={a} model={model} states={len(sts)} depth0={d0} depth1={len(sts) - d0} "
            f"owner_tests={tests} outputs={len(found)} verdict={'OUTPUT' if found else 'NO_OUTPUT_WITH_<=1_ROTATION'}"
            f" [{time.time() - t0:.0f}s]")
        for conv, o, tags, l1, l2, e, big in found[:3]:
            out(f"    witness conv={conv} owner={names[o] if o is not None else None} via={tags[:2]} "
                f"literal_lb4r={l1} literal_mine={l2} efx0_raw={e} bundles>2={big}")
    out(f"# finished in {time.time() - T0:.0f}s")


# ----------------------------------------------------------------------------------------------------------------
# K4.D on HH_3, HH_4 (d2_check.py)
def d2_main():
    for t in (3, 4):
        names, goods, v = build_HH(t)
        my = Model(v); inst = M.Inst(v)
        a1, a2 = names.index("x12A"), names.index("x12B")
        tau = None
        for h in range(my.n):
            st, order = my.phase1([a1, h])
            ins = [x for x, f, k in order if k == "I"]
            if len(ins) >= 2 and ins[0] == a1 and ins[1] == a2:
                tau = [a1, h]; break
        print(f"HH_{t}: tau = {tau}; insertion steps {[names[x] for x, f, k in order if k == 'I']}")
        done = False
        for pol in ("shrink", "envyFree", "none"):
            s1, steps = my.uprun(st, pol)
            for o in [None] + list(range(my.n)):
                ok, X = my.output(s1, o, "bundle")
                if ok:
                    lit, why = my.output_literal(s1, o, X, "bundle")
                    lit2 = M.output_check(inst, my_to_lb(s1), o, X, "bundle")
                    okA, _ = M.output_sat(inst, my_to_lb(s1), o, "bundle", backend="milp")
                    e, big = efx0_raw(v, X)
                    bund = [[goods[g] for g in range(my.m) if X[g] == i] for i in range(my.n)]
                    print(f"  policy {pol}, owner {names[o] if o is not None else None}: Output (my MILP), literal checks "
                          f"{lit}/{lit2}, lb4r MILP agrees {okA}, raw EFX0 {e}, bundles above two goods {big}")
                    print("   ", "; ".join(f"{names[i]}:{','.join(b)}" for i, b in enumerate(bund) if len(b) > 1 or True))
                    done = True
                    break
            if done:
                break
        if not done:
            print("  no Output without rotation")


# ----------------------------------------------------------------------------------------------------------------
# validation against lb4r.py (validate_mine.py)
def to_lb(st):
    return (tuple(-1 if b is None else b for b in st["base"]), tuple(-1 if p is None else p for p in st["pick"]),
            tuple(i in st["marked"] for i in range(len(st["pick"]))))


def compare(v, taus, depth, convs=("bundle", "base"), stats=None):
    inst = M.Inst(v); my = Model(v)
    for tau in taus:
        s_lb, _ = M.phase1_state(inst, tau)
        s_my, _ = my.phase1(tau)
        assert to_lb(s_my) == s_lb, ("phase1", tau)
        for pol in ("shrink", "envyFree", "none"):
            a, _ = M.up_run(inst, s_lb, pol)
            b, _ = my.uprun(s_my, pol)
            assert to_lb(b) == a, ("uprun", tau, pol)
            frontier = [b]
            seen = {to_lb(b)}
            allst = [b]
            for d in range(depth):
                nxt = []
                for s in frontier:
                    succ_lb = set(M.rot_steps(inst, to_lb(s)).keys())
                    succ_my = my.rotsteps(s)
                    assert set(to_lb(x[0]) for x in succ_my) == succ_lb, ("rot", tau, pol, d)
                    for s2, c, O in succ_my:
                        k = to_lb(s2)
                        if k not in seen:
                            seen.add(k); nxt.append(s2); allst.append(s2)
                frontier = nxt
            for s in allst:
                for conv in convs:
                    for o in [None] + list(range(my.n)):
                        ok_lb, _ = M.output_sat(inst, to_lb(s), o, conv)
                        ok_my, X = my.output(s, o, conv)
                        stats["tests"] += 1
                        if ok_lb != ok_my:
                            stats["mismatch"] += 1
                            print("MISMATCH", v, tau, pol, conv, o, ok_lb, ok_my)
                        if ok_my:
                            stats["sat"] += 1
                            l1, why = my.output_literal(s, o, X, conv)
                            l2 = M.output_check(inst, to_lb(s), o, X, conv)
                            e, _ = efx0_raw(v, X)
                            if not (l1 and l2 and e):
                                stats["badwit"] += 1
                                print("BAD WITNESS", v, tau, pol, conv, o, why, l2, e)


def rand_profile(rng, n, m):
    """Random instance, 3 or 4 relevant goods per agent, distinct values; not necessarily a core."""
    v = [[0] * m for _ in range(n)]
    for i in range(n):
        d = rng.choice([3, 4])
        gs = rng.sample(range(m), d)
        vals = rng.sample(range(1, 11), d)
        for g, x in zip(gs, vals):
            v[i][g] = x
    for g in range(m):
        if all(v[i][g] == 0 for i in range(n)):
            i = rng.randrange(n)
            v[i][g] = 11 + g
    return v


def validate_main(argv):
    argv = ["validate"] + argv          # argv[1], argv[2], argv[3] as in the scratch script's sys.argv
    stats = {"tests": 0, "mismatch": 0, "sat": 0, "badwit": 0}
    t0 = time.time()
    skip_h = len(argv) > 3
    for t in (() if skip_h else (1, 2)):
        names, goods, v = build_H(t)
        compare(v, [[a] for a in range(len(v))] + [[]], 2 if t == 1 else 1, stats=stats)
        print(f"H_{t}", stats, f"{time.time() - t0:.0f}s", flush=True)
    if not skip_h:
        names, goods, v = build_Hq(1)
        compare(v, [[a] for a in range(len(v))], 2, stats=stats)
    print("Hq_1", stats, f"{time.time() - t0:.0f}s", flush=True)
    rng = random.Random(int(argv[1]) if len(argv) > 1 else 1)
    R = int(argv[2]) if len(argv) > 2 else 200
    for r in range(R):
        n = rng.choice([2, 3, 4]); m = rng.randint(max(n + 1, 4), min(3 * n, 9))
        v = rand_profile(rng, n, m)
        compare(v, [[a] for a in range(n)], 2, stats=stats)
    print("random", R, stats, f"{time.time() - t0:.0f}s", flush=True)


def core_main():
    for nm, b in (("H3", lambda: build_H(3)), ("Hq3", lambda: build_Hq(3)), ("HH3", lambda: build_HH(3)),
                  ("HH4", lambda: build_HH(4))):
        names, goods, v = b()
        ok, msgs, bigtop, n4 = check_core(names, goods, v)
        print(nm, "n =", len(names), "m =", len(goods), "core+strict:", ok, msgs, "big-top:", bigtop, "4-good:", n4)


if __name__ == "__main__":
    cmd, rest = sys.argv[1], sys.argv[2:]
    if cmd == "exact":
        exact_main(rest)
    elif cmd == "d2":
        d2_main()
    elif cmd == "validate":
        validate_main(rest)
    elif cmd == "core":
        core_main()
