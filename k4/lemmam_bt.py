"""Lemma M of k4/rulef.md by the big-top induction (k4/lemmam_bt.md): tools.

Written for workstream proof/k4-lemmam-bt on PR #33's independent model of LB4r (k4/c4_verify_H/lb4r.py, a
transcription of lean/EFX/LB4R.lean); no code from k4/rulef.c. Lemma K's deficit is computed here from the text of
k4/rulef.md §2 (with Remark 4: kept-out sets may hold goods the served agent does not value).

  make_inst(sets, vals)          instance (lb4r.Inst) of a profile given as goods lists and values in the same order
  bigtops(inst)                  the big-top agents (four goods, top worth more than the next two together)
  run_state(inst, a, pol)        the state after Phase 1(tau_a) (a first, then index order) and upgrades of pol
  kdef(inst, s, o, K)            Lemma K's deficit of (o, K) at the state s, with a least service
  kdef_best(inst, s)             least Lemma K deficit over the owners and kept sets (-inf when omega <= 0)
  classes(inst, a, pols)         K0 / K1 of the first agent a (K1: some single RotStep reaches deficit <= 0)
  analyse_r(inst, s, run)        owner r of the state: exposed agents, frozen/upgraded/free, kappa0, sigma_F (rulef.md §6)
"""
import itertools, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'c4_verify_H'))
import lb4r as M

NEG = float('-inf')
INF = float('inf')
POLS = ('shrink', 'envyFree', 'none')


def make_inst(sets, vals):
    m = 1 + max(g for S in sets for g in S)
    v = [[0] * m for _ in sets]
    for i, (S, V) in enumerate(zip(sets, vals)):
        for g, x in zip(S, V):
            v[i][g] = x
    return M.Inst(v)


def ranking(inst, i):
    return sorted(inst.R[i], key=lambda g: -inst.v[i][g])


def is_bigtop(inst, i):
    r = ranking(inst, i)
    v = inst.v[i]
    return len(r) == 4 and v[r[0]] > v[r[1]] + v[r[2]]


def bigtops(inst):
    return [i for i in range(inst.n) if is_bigtop(inst, i)]


def val(inst, i, S):
    return sum(inst.v[i][g] for g in S)


def threatened(inst, x, L, H):
    """max over h in L of v_x(L - h) > v_x(H): agent x holding H strongly envies L."""
    L = list(L)
    if not L:
        return False
    tot = val(inst, x, L)
    return max(tot - inst.v[x][h] for h in L) > val(inst, x, H)


def run_state(inst, a, pol):
    s, run = M.phase1_state(inst, (a,))
    s, steps = M.up_run(inst, s, pol)
    return s, run, steps


def bases(inst, s):
    return [M.base_of(inst, s, i) for i in range(inst.n)]


def junk(inst, s):
    return [g for g in range(inst.m) if s[0][g] == -1]


def kdef(inst, s, o, K, needs=None, want=False):
    """Lemma K (k4/rulef.md §2) for owner o and kept set K: (deficit, service) where the service maps each threatened
    agent to ('s', {g}) or ('r', D). INF if some threatened agent has no option."""
    n = inst.n
    if needs is None:
        needs = M.all_needs(inst, s)
    B = bases(inst, s)
    J = junk(inst, s)
    Wo = set(B[o]) | set(J)
    vBK = val(inst, o, set(B[o]) | set(K))
    NA = set(g for g in needs[o] if inst.v[o][g] > vBK)
    for i in range(n):
        if i != o:
            NA |= needs[i]
    capK = []
    for x in range(n):
        frz = len(B[x]) == 1 and B[x][0] in NA
        capK.append(0 if frz else max(0, 2 - len(B[x])))
    kappa = sum(capK[x] for x in range(n) if x != o)
    JK = [g for g in J if g not in K]
    opts = []
    for x in range(n):
        if x == o or not threatened(inst, x, Wo, B[x]):
            continue
        ox = []
        if capK[x] >= 1 and len(B[x]) <= 1:
            for g in JK:
                if not threatened(inst, x, Wo - {g}, B[x] + [g]):
                    ox.append(('s', frozenset([g])))
        # threatened(x, Wo - D, B_x) depends on D only through D ∩ R_x and whether Wo - D lies inside R_x, so the
        # minimal kept-out sets are among the subsets of JK ∩ R_x, alone or with every good of JK outside R_x
        # (k4/rulef.md §2, Remark 4)
        inR = [g for g in JK if inst.v[x][g] > 0]
        out = frozenset(g for g in JK if inst.v[x][g] == 0)
        mins = []
        for extra in ([frozenset()] + ([out] if out else [])):
            for r in range(len(inR) + 1):
                for D in itertools.combinations(inR, r):
                    D = frozenset(D) | extra
                    if any(E <= D for E in mins):
                        continue
                    if not threatened(inst, x, Wo - D, B[x]):
                        mins.append(D)
        ox += [('r', D) for D in mins]
        if not ox:
            return INF, None
        opts.append((x, ox))
    # an upper bound UB by a greedy service; an option with more than UB goods is in no least service, so it is
    # dropped (this removes the large kept-out sets of Remark 4 on big instances)
    U, G = frozenset(), frozenset()
    for x, ox in opts:
        cand = [(len(U | S), kind, S) for kind, S in ox if not (kind == 's' and S & G)]
        if not cand:
            U = None
            break
        _, kind, S = min(cand, key=lambda c: c[0])
        U = U | S
        if kind == 's':
            G = G | S
    if U is not None:
        UB = len(U)
        opts = [(x, [(kind, S) for kind, S in ox if len(S) <= UB]) for x, ox in opts]
    # agents whose options share no good are independent: the least service is the sum over the components of the
    # graph "x ~ y if some option of x meets some option of y"
    goods_of = [frozenset().union(*[S for _, S in ox]) for _, ox in opts]
    comp = list(range(len(opts)))

    def find(i):
        while comp[i] != i:
            comp[i] = comp[comp[i]]
            i = comp[i]
        return i
    for i in range(len(opts)):
        for j in range(i):
            if goods_of[i] & goods_of[j]:
                comp[find(i)] = find(j)
    groups = {}
    for i in range(len(opts)):
        groups.setdefault(find(i), []).append(opts[i])
    total, service = 0, {}
    for grp in groups.values():
        grp = sorted(grp, key=lambda xo: len(xo[1]))
        best = [INF, None]

        def dfs(i, U, G, ch):
            if len(U) >= best[0]:
                return
            if i == len(grp):
                best[0] = len(U)
                best[1] = dict(ch)
                return
            x, ox = grp[i]
            free = [(kind, S) for kind, S in ox if kind == 'r' and S <= U]
            for kind, S in (free[:1] if free else sorted(ox, key=lambda kS: len(kS[1] - U))):
                if kind == 's' and (S & G):
                    continue
                ch.append((x, (kind, S)))
                dfs(i + 1, U | S, G | S if kind == 's' else G, ch)
                ch.pop()
        dfs(0, frozenset(), frozenset(), [])
        if best[0] == INF:
            return INF, None
        total += best[0]
        service.update(best[1])
    return total - kappa, service


def owners(inst, s, needs=None):
    if needs is None:
        needs = M.all_needs(inst, s)
    NA = M.NA_of(needs)
    fr = M.frozen_pre(inst, s, NA)
    B = bases(inst, s)
    big = [o for o in range(inst.n) if len(B[o]) >= 3]
    if big:
        return big if len(big) == 1 and not fr[big[0]] else []
    return [o for o in range(inst.n) if not fr[o]]


def kdef_best(inst, s, want=False, owner_list=None):
    """Least Lemma K deficit over owners and kept sets K inside J ∩ R_o; -inf if omega <= 0 (and no 3-good base)."""
    needs = M.all_needs(inst, s)
    B = bases(inst, s)
    if all(len(b) <= 2 for b in B) and M.omega(inst, s, needs) <= 0:
        return (NEG, None) if want else NEG
    best, arg = INF, None
    J = junk(inst, s)
    for o in (owners(inst, s, needs) if owner_list is None else owner_list):
        cand = [g for g in J if inst.v[o][g] > 0]
        for r in range(len(cand) + 1):
            for K in itertools.combinations(cand, r):
                d, sv = kdef(inst, s, o, set(K), needs)
                if d < best:
                    best, arg = d, (o, K, sv)
                    if best <= 0 and not want:
                        return best
    return (best, arg) if want else best


def k1(inst, s, want=False):
    """Some single RotStep from s reaches a state with Lemma K deficit <= 0 (or omega <= 0, no base of 3+ goods)."""
    for s2, desc in M.rot_steps(inst, s).items():
        if kdef_best(inst, s2) <= 0:
            return (True, desc, s2) if want else True
    return (False, None, None) if want else False


def classes(inst, a, pols=('shrink', 'envyFree')):
    """(K0 policies, K1 policies) of first agent a."""
    k0, k1p = [], []
    for pol in pols:
        s, run, _ = run_state(inst, a, pol)
        if kdef_best(inst, s) <= 0:
            k0.append(pol)
        elif k1(inst, s):
            k1p.append(pol)
    return k0, k1p


def proc_order(run):
    return [x for x, f, kind in run]


def analyse_r(inst, s, run, needs=None):
    """The owner r (last-processed unmarked agent) of a state, W = B_r ∪ J, exposed agents E with their kind
    (free / frozen / upgraded), kappa0 (slot places of the free unexposed agents other than r) and the least service
    sigma_F of the exposed agents that are not free (K = ∅, Lemma K's options), as in k4/rulef.md §6."""
    if needs is None:
        needs = M.all_needs(inst, s)
    NA = M.NA_of(needs)
    fr = M.frozen_pre(inst, s, NA)
    marked = s[2]
    order = proc_order(run)
    r = [x for x in order if not marked[x]][-1]
    B = bases(inst, s)
    J = junk(inst, s)
    W = set(B[r]) | set(J)
    E = [x for x in range(inst.n) if x != r and threatened(inst, x, W, B[x])]
    kind = {}
    for x in range(inst.n):
        kind[x] = 'U' if marked[x] else ('F' if fr[x] else 'T')
    kappa0 = sum(max(0, 2 - len(B[x])) for x in range(inst.n) if x != r and kind[x] == 'T' and x not in E)
    return dict(r=r, W=W, E=E, kind=kind, kappa0=kappa0, frozen_r=fr[r])
