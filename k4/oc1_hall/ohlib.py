"""Shared code for the OC1 Hall-count workstream (k4/oc1_hall.md).

Instances are (name, sets, vals, m) as in k4/sdc (sets[i] = the goods agent i values, vals[i] their values).  Ties are
broken by good index exactly as in k4/sdc/sdc_orders.sd: an agent ranks g above h iff (v(g), -g) > (v(h), -h).

This module re-implements, from the raw EFX0 definition and without SAT:
  * serial-dictatorship picks of an order;
  * the one-absorber completion test of k4/sdc/oc_absorb.extends_A (A = 1), by enumeration (`absorb_brute`);
  * the slot form of that test at single-good bases (`slot_test`, k4/oc1_hall.md Lemma 1).
"""
import os, sys, json, gzip, random, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
SDC = os.path.join(ROOT, 'k4', 'sdc')
if SDC not in sys.path: sys.path.insert(0, SDC)
import _paths  # noqa: E402  (k4/sdc paths: de4, k3)


class Inst:
    def __init__(self, sets, vals, m, name=''):
        self.name = name
        self.n = len(sets); self.m = m
        self.sets = [list(s) for s in sets]; self.vals = [list(v) for v in vals]
        self.R = [set(s) for s in sets]
        self.v = [dict(zip(s, vv)) for s, vv in zip(sets, vals)]
        # strict rank key: (value, -index)
        self.key = [{g: (self.v[i][g], -g) for g in self.R[i]} for i in range(self.n)]

    def val(self, i, S):
        v = self.v[i]
        return sum(v.get(g, 0) for g in S)

    def better(self, i, g, h):
        """i strictly prefers good g to good h (h may be None)"""
        if g not in self.R[i]: return False
        if h is None: return True
        if h not in self.R[i]: return True
        return self.key[i][g] > self.key[i][h]


def picks(I, order):
    left = set(range(I.m)); Y = [None] * I.n
    for i in order:
        av = [g for g in I.R[i] if g in left]
        if av:
            g = max(av, key=lambda h: I.key[i][h]); Y[i] = g; left.discard(g)
    return tuple(Y)


def efx0(I, X):
    """raw EFX0: for all i != j and every g in X_j, v_i(X_i) >= v_i(X_j minus g)"""
    own = [I.val(i, X[i]) for i in range(I.n)]
    for j in range(I.n):
        if len(X[j]) < 2: continue
        for i in range(I.n):
            if i == j: continue
            vj = [I.v[i].get(g, 0) for g in X[j]]
            if sum(vj) - min(vj) > own[i]: return False
    return True


def bundles_of(I, base):
    B = [[] for _ in range(I.n)]
    for g, a in enumerate(base):
        if a is not None and a >= 0: B[a].append(g)
    return B


def base_of_picks(I, Y):
    base = [-1] * I.m
    for i, g in enumerate(Y):
        if g is not None: base[g] = i
    return tuple(base)


def absorb_brute(I, base, owners=None, witness=False):
    """one-absorber completion of the bases by enumeration: some agent o (the absorber) takes any number of junk goods,
    every other agent at most one; complete and EFX0 by the raw definition.  owners: restrict o.  Returns the set of
    working absorbers (or (o, X) with witness)."""
    B = bundles_of(I, base); J = [g for g in range(I.m) if base[g] < 0]
    good = set()
    for o in (owners if owners is not None else range(I.n)):
        others = [i for i in range(I.n) if i != o]
        found = None
        for k in range(0, min(len(J), len(others)) + 1):
            for K in itertools.combinations(J, k):
                L = [g for g in J if g not in K]
                for who in itertools.permutations(others, k):
                    X = [list(b) for b in B]
                    for g, a in zip(K, who): X[a].append(g)
                    X[o] += L
                    if efx0(I, X): found = X; break
                if found: break
            if found: break
        if found:
            if witness: return o, found
            good.add(o)
    if witness: return None
    return good


# ----------------------------------------------------------------------------------------------- picks structure
class Picks:
    """structure of serial-dictatorship picks Y (k4/sdc.md §30): wants, frozen set F, junk J"""
    def __init__(self, I, Y):
        self.I = I; self.Y = Y; n = I.n
        self.J = [g for g in range(I.m) if g not in set(y for y in Y if y is not None)]
        self.pv = [I.v[i].get(Y[i], 0) if Y[i] is not None else 0 for i in range(n)]
        self.W = [[i for i in range(n) if i != j and Y[j] is not None and I.v[i].get(Y[j], 0) > self.pv[i]]
                  for j in range(n)]                       # W[j]: the agents wanting j's pick
        self.F = [j for j in range(n) if self.W[j]]
        self.Jv = [[g for g in self.J if g in I.R[i]] for i in range(n)]   # each agent's junk goods
        self.D = [x for x in self.F if self.Jv[x]]         # dangerous agents (frozen, value some junk)


def threatened(I, i, ti, Xo):
    """does bundle Xo threaten agent i holding value ti? (raw: some h in Xo with v_i(Xo - h) > ti)"""
    vs = [I.v[i].get(g, 0) for g in Xo]
    return len(Xo) >= 2 and sum(vs) - min(vs) > ti


def slot_test(P, o, frozen_slots=True, witness=False):
    """Lemma 1 (k4/oc1_hall.md): the one-absorber completions of the picks with absorber o are exactly the slot
    assignments z (each agent j != o at most one junk good z_j, distinct) with
      (S1) if j holds a pick and a slot good, every agent i wanting Y_j has v_i(X_i) >= v_i(Y_j);
      (S2) X_o = {Y_o} + (J minus the slot goods) threatens nobody.
    frozen_slots=False: frozen agents take no slot (the GDT shape)."""
    I = P.I; Y = P.Y; n = I.n; J = P.J
    others = [j for j in range(n) if j != o and (frozen_slots or j not in P.F)]
    for k in range(0, min(len(J), len(others)) + 1):
        for K in itertools.combinations(J, k):
            L = [g for g in J if g not in K]
            Xo = ([Y[o]] if Y[o] is not None else []) + L
            for who in itertools.permutations(others, k):
                z = dict(zip(who, K))
                t = [P.pv[i] + I.v[i].get(z.get(i), 0) for i in range(n)]
                t[o] = I.val(o, Xo)
                ok = True
                for j, g in z.items():          # (S1)
                    if Y[j] is None: continue
                    if any(t[i] < I.v[i].get(Y[j], 0) for i in P.W[j]): ok = False; break
                if not ok: continue
                if any(threatened(I, i, t[i], Xo) for i in range(n) if i != o): continue   # (S2)
                if witness: return z
                return True
    return None if witness else False


# ----------------------------------------------------------------------------------------------- general states
def wants_good(I, B, i, g):
    """agent i wants good g (held by someone else): v_i(g) > v_i(B_i)"""
    return g not in B[i] and I.v[i].get(g, 0) > I.val(i, B[i])


def frozen_set(I, base):
    """single-good holders whose good some other agent wants"""
    B = bundles_of(I, base)
    return [j for j in range(I.n) if len(B[j]) == 1 and any(wants_good(I, B, i, B[j][0]) for i in range(I.n) if i != j)]


def shaped_completion(I, base, o, holders, witness=False):
    """complete EFX0 allocation (raw definition) keeping the bases, giving at most one junk good to each agent of
    `holders` (o excluded), nothing to the others, and the rest to o"""
    B = bundles_of(I, base); J = [g for g in range(I.m) if base[g] < 0]
    hs = [h for h in holders if h != o]
    for k in range(0, min(len(J), len(hs)) + 1):
        for K in itertools.combinations(J, k):
            L = [g for g in J if g not in K]
            for who in itertools.permutations(hs, k):
                X = [list(b) for b in B]
                for g, a in zip(K, who): X[a].append(g)
                X[o] += L
                if efx0(I, X): return X if witness else True
    return None if witness else False


def gdt_shape(I, base, owners='unfrozen-single', witness=False, hold='unfrozen-single'):
    """GDT-shaped one-absorber completion: slot holders are the single-good (or empty) holders that are not frozen
    (hold='unfrozen-single'; 'single': every single-good or empty holder; 'all': every agent); the owner is an
    unfrozen single-good holder (owners='unfrozen-single') or any agent ('any')"""
    B = bundles_of(I, base); F = set(frozen_set(I, base))
    us = [j for j in range(I.n) if len(B[j]) <= 1 and j not in F]
    holders = us if hold == 'unfrozen-single' else ([j for j in range(I.n) if len(B[j]) <= 1] if hold == 'single' else list(range(I.n)))
    os_ = us if owners == 'unfrozen-single' else range(I.n)
    for o in os_:
        r = shaped_completion(I, base, o, holders, witness)
        if r: return (o, r) if witness else True
    return None if witness else False


# ----------------------------------------------------------------------------------------------- the deficit count
def safe(I, i, ti, Xo):
    return not threatened(I, i, ti, Xo)


def deficit(I, base, o, holders, frozen_like):
    """the S* deficit of owner o (k4/oc1_hall.md §4): the least |H| - kappa over kept-out sets H of junk goods and
    injective partial assignments phi of goods of H to the holders (kappa = |holders - {o}|), such that with
    X_o = B_o + (J - H) every agent other than o is safe; goods of H not given to a holder sit in virtual slots.
    Agents in frozen_like (frozen and multi-good holders) take nothing.  Returns (deficit, H, phi) or (None,..)."""
    B = bundles_of(I, base); J = [g for g in range(I.m) if base[g] < 0]
    hs = [h for h in holders if h != o]; kappa = len(hs)
    best = None
    pv = [I.val(i, B[i]) for i in range(I.n)]
    for r in range(0, len(J) + 1):
        if best is not None and r - kappa >= best[0]: break
        for H in itertools.combinations(J, r):
            Xo = B[o] + [g for g in J if g not in H]
            if any(not safe(I, x, pv[x], Xo) for x in frozen_like if x != o): continue
            # each holder: safe with nothing, or with some good of H it values
            need = []; ok = True
            for u in hs:
                if safe(I, u, pv[u], Xo): continue
                opts = [g for g in H if g in I.R[u] and safe(I, u, pv[u] + I.v[u][g], Xo)]
                if not opts: ok = False; break
                need.append((u, opts))
            if not ok: continue
            # distinct goods for the needy holders (tiny bipartite matching by search)
            def match(k, used):
                if k == len(need): return {}
                u, opts = need[k]
                for g in opts:
                    if g in used: continue
                    rest = match(k + 1, used | {g})
                    if rest is not None: rest[u] = g; return rest
                return None
            phi = match(0, frozenset())
            if phi is None: continue
            best = (r - kappa, H, phi); break
    return best if best is not None else (None, None, None)


def s_star_deficits(I, base, owners=None):
    """deficit of every owner under S* (owner any agent; holders the unfrozen single-good or empty holders)"""
    B = bundles_of(I, base); F = set(frozen_set(I, base))
    holders = [j for j in range(I.n) if len(B[j]) <= 1 and j not in F]
    frozen_like = [j for j in range(I.n) if j not in holders]
    out = {}
    for o in (owners if owners is not None else range(I.n)):
        out[o] = deficit(I, base, o, holders, frozen_like)
    return out


# ----------------------------------------------------------------------------------------------- Lemma 2, constructively
def robust_in(I, i, Xi, Rp):
    """Xi robust inside the relevant set Rp: v_i(Xi) >= v_i(Rp - Xi)"""
    return I.val(i, Xi) >= I.val(i, [g for g in Rp if g not in Xi])


def lemma2_build(I, base, o, H, phi, holders, maxit=1000):
    """the (<=) construction of Lemma 2: phi maps exposed holders to goods of H; the other goods of H go to unexposed
    holders; then Theorem DT's moves (m1), (m2) for the remaining holders, with goods from L = J - H.  Returns the
    allocation (or None if a step is impossible; that would refute the lemma under its hypotheses)."""
    B = bundles_of(I, base); J = [g for g in range(I.m) if base[g] < 0]
    hs = [h for h in holders if h != o]
    X = [list(b) for b in B]
    W_o = B[o] + J
    WoH = [g for g in W_o if g not in H]
    pv = [I.val(i, B[i]) for i in range(I.n)]
    exposed = [u for u in hs if threatened(I, u, pv[u], WoH)]
    used = set()
    for u, g in phi.items(): X[u].append(g); used.add(g)
    free = [u for u in hs if u not in exposed and u not in phi]
    for g in H:
        if g in used: continue
        if not free: return None
        X[free.pop()].append(g); used.add(g)
    movers = [u for u in exposed if u not in phi]
    L = [g for g in J if g not in H]
    m = {}
    for it in range(maxit):
        Xo = B[o] + L
        bad = [u for u in movers if threatened(I, u, pv[u] + I.v[u].get(m.get(u), 0), Xo)]
        if not bad: break
        u = bad[0]; t = pv[u] + I.v[u].get(m.get(u), 0)
        # a danger set: (Xo - h) & R_u for a threatening h
        h = min(Xo, key=lambda g: I.v[u].get(g, 0))
        T = [g for g in Xo if g != h and g in I.R[u]]
        cand = [g for g in T if g in L]
        if not cand: return None
        g = max(cand, key=lambda q: I.key[u][q])
        if u in m: L.append(m[u])
        m[u] = g; L.remove(g)
    else:
        return None
    for u, g in m.items(): X[u].append(g)
    X[o] = X[o] + L
    return X
