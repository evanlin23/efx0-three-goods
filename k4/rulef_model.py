"""Lemma K of k4/rulef.md §2 in Python, written from the text on PR #33's independent model of LB4r
(k4/c4_verify_H/lb4r.py, a transcription of lean/EFX/LB4R.lean), without code from k4/rulef.c.

  deficit_K(inst, s)            least Lemma K deficit over the owners o and kept sets K of the state s (-inf: omega <= 0)
  witness_K(inst, s)            an (o, K, completion X) realizing a deficit <= 0, with X built as in the proof
  run_state(inst, a, pol)       the state after Phase 1(tau_a) (tau_a = (a, then index order)) and upgrades of pol
Every witness is checked with lb4r.output_check (the literal Output of LB4R.lean, owner's needs from the bundle) and
against the raw EFX0 definition (check_efx0)."""
import itertools, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'c4_verify_H'))
import lb4r as M

NEG = float('-inf')
XKEEP = False   # as k4/rulef.c -Y1: kept-out sets may also hold every allowed good outside R_x
COMBO = False   # Lemma K' (k4/rulef.md §2, Remark 5): an agent may take a slot good and keep a set out at once
INF = float('inf')


def make_inst(sets, vals):
    m = 1 + max(g for S in sets for g in S)
    v = [[0] * m for _ in sets]
    for i, (S, V) in enumerate(zip(sets, vals)):
        for g, x in zip(S, V):
            v[i][g] = x
    return M.Inst(v)


def run_state(inst, a, pol):
    s, run = M.phase1_state(inst, (a,))
    s, _ = M.up_run(inst, s, pol)
    return s, run


def val(inst, i, S):
    return sum(inst.v[i][g] for g in S)


def threatened(inst, x, L, H):
    """max over h in L of v_x(L - h) > v_x(H) (the raw strong-envy test)."""
    L = list(L)
    if not L:
        return False
    tot = val(inst, x, L)
    return max(tot - inst.v[x][h] for h in L) > val(inst, x, H)


def owners(inst, s, needs, NA):
    """Lemma K's owners: an agent that is not frozen (Frozen of PreAllocK: a one-good base in NA, marked or not);
    if some base has three or more goods, only its agent."""
    fr = M.frozen_pre(inst, s, NA)
    big = [o for o in range(inst.n) if len(M.base_of(inst, s, o)) >= 3]
    if big:
        return big if len(big) == 1 and not fr[big[0]] else []
    return [o for o in range(inst.n) if not fr[o]]


def services(inst, s, o, K, needs):
    """Least service size and the slot capacity for owner o and kept set K; returns (deficit, service) or (INF, None)."""
    base, pick, marked = s
    n, m = inst.n, inst.m
    J = [g for g in range(m) if base[g] == -1]
    Bo = M.base_of(inst, s, o)
    Wo = set(Bo) | set(J)
    vBK = val(inst, o, set(Bo) | set(K))
    NoK = frozenset(g for g in needs[o] if inst.v[o][g] > vBK)
    NA = set(NoK)
    for i in range(n):
        if i != o:
            NA |= needs[i]
    bases = [M.base_of(inst, s, i) for i in range(n)]
    capK = []
    for x in range(n):
        frz = len(bases[x]) == 1 and bases[x][0] in NA
        capK.append(0 if frz else max(0, 2 - len(bases[x])))
    kappa = sum(capK[x] for x in range(n) if x != o)
    JK = [g for g in J if g not in K]
    opts = []
    for x in range(n):
        if x == o or not threatened(inst, x, Wo, bases[x]):
            continue
        ox = []
        if capK[x] >= 1:
            for g in JK:
                if not threatened(inst, x, Wo - {g}, bases[x] + [g]):
                    ox.append(('s', frozenset([g])))
        cand = [g for g in JK if inst.v[x][g] > 0]
        JKX = JK
        mins = []
        for r in range(len(cand) + 1):
            for D in itertools.combinations(cand, r):
                D = frozenset(D)
                if any(E <= D for E in mins):
                    continue
                if not threatened(inst, x, Wo - D, bases[x]):
                    mins.append(D)
        if XKEEP:
            non = frozenset(g for g in JKX if inst.v[x][g] == 0)
            if non:
                for r in range(len(cand) + 1):
                    for D in itertools.combinations(cand, r):
                        D = frozenset(D) | non
                        if any(E <= D for E in mins):
                            continue
                        if not threatened(inst, x, Wo - D, bases[x]):
                            mins.append(D)
        ox += [('r', D) for D in mins]
        if COMBO and capK[x] >= 1:
            for g in JK:
                if not threatened(inst, x, Wo - {g}, bases[x] + [g]):
                    continue
                Wg = Wo - {g}
                cg = [h for h in cand if h != g]
                ming = []
                extra = [frozenset()]
                if XKEEP:
                    nong = frozenset(h for h in JKX if inst.v[x][h] == 0 and h != g)
                    if nong:
                        extra.append(nong)
                for ex in extra:
                    for r in range(len(cg) + 1):
                        for D in itertools.combinations(cg, r):
                            D = frozenset(D) | ex
                            if any(E <= D for E in ming):
                                continue
                            if not threatened(inst, x, Wg - D, bases[x] + [g]):
                                ming.append(D)
                ox += [(('sr', g), D | {g}) for D in ming]
        if not ox:
            return INF, None
        opts.append((x, ox))
    best = [INF, None]

    def slot_of(kind, S):
        if kind == 's':
            return S
        if isinstance(kind, tuple):
            return frozenset([kind[1]])
        return frozenset()

    def dfs(i, U, G, ch):
        if len(U) >= best[0]:
            return
        if i == len(opts):
            best[0] = len(U); best[1] = list(ch); return
        x, ox = opts[i]
        for kind, S in ox:
            sl = slot_of(kind, S)
            if sl & G:
                continue
            dfs(i + 1, U | S, G | sl, ch + [(x, kind, S)])
    dfs(0, frozenset(), frozenset(), [])
    if best[1] is None:
        return INF, None
    return best[0] - kappa, (best[1], capK)


def all_min_services(inst, s, o, needs):
    """every least ∅-service of the agents threatened by W_o (K = ∅): (deficit, [service, ...], capK, E)"""
    base, pick, marked = s
    n, m = inst.n, inst.m
    J = [g for g in range(m) if base[g] == -1]
    Bo = M.base_of(inst, s, o)
    Wo = set(Bo) | set(J)
    NA = set(needs[o])
    for i in range(n):
        if i != o:
            NA |= needs[i]
    bases = [M.base_of(inst, s, i) for i in range(n)]
    capK = [0 if (len(bases[x]) == 1 and bases[x][0] in NA) else max(0, 2 - len(bases[x])) for x in range(n)]
    kappa = sum(capK[x] for x in range(n) if x != o)
    opts = []
    for x in range(n):
        if x == o or not threatened(inst, x, Wo, bases[x]):
            continue
        ox = []
        if capK[x] >= 1:
            ox += [('s', frozenset([g])) for g in J if not threatened(inst, x, Wo - {g}, bases[x] + [g])]
        cand = [g for g in J if inst.v[x][g] > 0]
        JKX = J
        mins = []
        for r in range(len(cand) + 1):
            for D in itertools.combinations(cand, r):
                D = frozenset(D)
                if any(E <= D for E in mins):
                    continue
                if not threatened(inst, x, Wo - D, bases[x]):
                    mins.append(D)
        if XKEEP:
            non = frozenset(g for g in JKX if inst.v[x][g] == 0)
            if non:
                for r in range(len(cand) + 1):
                    for D in itertools.combinations(cand, r):
                        D = frozenset(D) | non
                        if any(E <= D for E in mins):
                            continue
                        if not threatened(inst, x, Wo - D, bases[x]):
                            mins.append(D)
        ox += [('r', D) for D in mins]
        if not ox:
            return INF, [], capK, [x for x, _ in opts] + [x]
        opts.append((x, ox))
    best = [INF, []]

    def dfs(i, U, G, ch):
        if len(U) > best[0]:
            return
        if i == len(opts):
            if len(U) < best[0]:
                best[0] = len(U); best[1] = []
            best[1].append(list(ch)); return
        x, ox = opts[i]
        for kind, S in ox:
            if kind == 's' and (S & G):
                continue
            dfs(i + 1, U | S, G | S if kind == 's' else G, ch + [(x, kind, S)])
    dfs(0, frozenset(), frozenset(), [])
    return best[0] - kappa, best[1], capK, [x for x, _ in opts]


def deficit_K(inst, s, want=False):
    needs = M.all_needs(inst, s)
    NA = M.NA_of(needs)
    big = any(len(M.base_of(inst, s, o)) >= 3 for o in range(inst.n))
    if not big and M.omega(inst, s, needs) <= 0:
        return (NEG, None) if want else NEG
    base = s[0]
    J = [g for g in range(inst.m) if base[g] == -1]
    best, wit = INF, None
    for o in owners(inst, s, needs, NA):
        JR = [g for g in J if inst.v[o][g] > 0]
        for r in range(len(JR) + 1):
            for K in itertools.combinations(JR, r):
                d, sv = services(inst, s, o, frozenset(K), needs)
                if d < best:
                    best, wit = d, (o, frozenset(K), sv)
    return (best, wit) if want else best


def witness_K(inst, s):
    """The completion of the proof of Lemma K for a deficit <= 0: slot goods into their agents' slots, the removal
    sets into the remaining slots, the rest of the junk to the owner. Returns (o, X) or None."""
    d, wit = deficit_K(inst, s, want=True)
    if d == NEG:
        needs = M.all_needs(inst, s)
        J = [g for g in range(inst.m) if s[0][g] == -1]
        X = list(s[0])
        caps = [2 - len(M.base_of(inst, s, i)) if not M.frozen_pre(inst, s, M.NA_of(needs))[i] else 0 for i in range(inst.n)]
        for g in J:
            for i in range(inst.n):
                if caps[i] > 0:
                    X[g] = i; caps[i] -= 1; break
        return None, X
    if d > 0:
        return None
    o, K, (ch, capK) = wit
    X = list(s[0])
    left = list(capK)
    left[o] = 0
    used = set()
    for x, kind, S in ch:
        if kind == 's' or isinstance(kind, tuple):
            g = kind[1] if isinstance(kind, tuple) else next(iter(S))
            X[g] = x; left[x] -= 1; used.add(g)
    for x, kind, S in ch:
        if kind != 's':
            for g in S:
                if g in used:
                    continue
                y = next(i for i in range(inst.n) if left[i] > 0)
                X[g] = y; left[y] -= 1; used.add(g)
    for g in range(inst.m):
        if X[g] == -1:
            X[g] = o
    return o, X


def check_efx0(inst, X):
    n, m = inst.n, inst.m
    bund = [[g for g in range(m) if X[g] == i] for i in range(n)]
    for i in range(n):
        vi = val(inst, i, bund[i])
        for j in range(n):
            if j != i and bund[j] and threatened(inst, i, bund[j], bund[i]):
                return False
    return True


def rot_deficit_K(inst, s):
    """Least Lemma K deficit over the states one RotStep (lean/EFX/LB4R.lean, every chain and base O) reaches from s,
    with the rotation that reaches it; (INF, None) if there is none."""
    best, arg = INF, None
    for s2, desc in M.rot_steps(inst, s).items():
        d = deficit_K(inst, s2)
        if d < best:
            best, arg = d, (s2, desc)
        if best == NEG:
            break
    return best, arg
