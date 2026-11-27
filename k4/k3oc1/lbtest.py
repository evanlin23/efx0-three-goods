"""The completion test in LB+'s terms (proofs/lb_last_step.md §2, Lemma 1), with every slot of size one:
a pre-allocation (picks and pair holders, as DE states), maximal upgrades (a b-holder whose c is junk and whose b
nobody needs takes c), then: |J| <= S (no owner), or some owner o (terminal or pair holder) and a hitting set H of
the sets pi_x = {b_x, c_x} & J (x exposed for o) with |H| <= S - cap(o), and no exposed pair inside base(o);
or an owner holding nothing that ends with two goods (omega = 1), which threatens nobody.
lb1(rk, m, base) returns a witness or None.  Compare with k3lib.completion (exhaustive)."""
import itertools
from k3lib import bundles


def upgrade(rk, m, base):
    """LB's upgrade loop to its fixpoint (UT); the fixpoint is unique (upgrades only shrink the need set)"""
    n = len(rk); nb = list(base)
    while True:
        B = bundles(nb, n); J = set(g for g in range(m) if nb[g] < 0)
        U = [len(B[i]) == 2 for i in range(n)]
        NA = set()
        for i in range(n):
            if U[i]: continue
            if not B[i]: NA |= set(rk[i])
            else:
                t = rk[i].index(B[i][0]); NA |= set(rk[i][:t])
        for k in range(n):
            if not U[k] and B[k] == [rk[k][1]] and rk[k][2] in J and rk[k][1] not in NA:
                nb[rk[k][2]] = k; break
        else:
            return tuple(nb)


def parts(rk, m, base):
    n = len(rk); B = bundles(base, n); J = [g for g in range(m) if base[g] < 0]
    U = [len(B[i]) == 2 for i in range(n)]
    NA = set()
    for i in range(n):
        if U[i]: continue
        if not B[i]: NA |= set(rk[i])
        else: NA |= set(rk[i][:rk[i].index(B[i][0])])
    F = [i for i in range(n) if not U[i] and B[i] and B[i][0] in NA]
    T = [i for i in range(n) if not U[i] and i not in F]
    return B, J, U, NA, F, T


def min_hit(sets, limit):
    goods = sorted(set(g for s in sets for g in s))
    for r in range(0, limit + 1):
        for H in itertools.combinations(goods, r):
            if all(set(s) & set(H) for s in sets): return H
    return None


def exposed(rk, base, o, B, J, U):
    W = set(J) | set(B[o])
    return [x for x in range(len(rk)) if x != o and not U[x] and B[x] == [rk[x][0]] and rk[x][1] in W and rk[x][2] in W]


def lb1(rk, m, base, do_upgrade=True):
    if do_upgrade: base = upgrade(rk, m, base)
    B, J, U, NA, F, T = parts(rk, m, base); S = len(T)
    if len(J) <= S: return ('no owner', None)
    for o in T + [i for i in range(len(rk)) if U[i]]:
        if not B[o] and len(J) - (S - 1) <= 2: return ('owner holding nothing, two junk goods', o)
        E = exposed(rk, base, o, B, J, U)
        if any({rk[x][1], rk[x][2]} <= set(B[o]) for x in E): continue
        H = min_hit([[g for g in (rk[x][1], rk[x][2]) if g in J] for x in E], S - (1 if o in T else 0))
        if H is not None: return ('owner', o, H)
    return None


def lb2(rk, m, base):
    """Exact one-absorber completion test for DE states (cross-checked against k3lib.completion).
    Choose a set S of upgrades (b-holders taking their junk c; the result must be valid: no b of an upgraded agent is
    needed); then an owner o (none, a terminal or a pair holder) and a set C of junk goods matched into one-good slots
    (terminals other than o: any junk good; pair holders u other than o that held their pair before (an upgrade uses
    the agent's one junk good): a junk good g such that no A-agent holding only its top has its pair inside
    base(u) + g), the rest J - C to o, such that X_o has at most two goods or contains no pair {b_x, c_x} of an
    A-agent x holding only its top."""
    n = len(rk); B0 = bundles(base, n); U0 = [len(b) >= 2 for b in B0]
    J0 = set(g for g in range(m) if base[g] < 0)
    Q = [i for i in range(n) if B0[i] == [rk[i][1]] and rk[i][2] in J0]
    for r in range(len(Q), -1, -1):
        for S in itertools.combinations(Q, r):
            nb = list(base)
            for i in S: nb[rk[i][2]] = i
            nb = tuple(nb)
            B, J, U, NA, F, T = parts(rk, m, nb)
            if any(rk[i][1] in NA for i in S): continue      # (V2) fails
            res = _owner_test(rk, m, nb, B, J, U, T, U0)
            if res: return res + (('upgrades', S),)
    return None


def lb2_owners(rk, m, base, allowed):
    """lb2 with the owner restricted to `allowed` (a set of agents; 'none' in it allows the no-owner completion)"""
    n = len(rk); B0 = bundles(base, n); U0 = [len(b) >= 2 for b in B0]
    J0 = set(g for g in range(m) if base[g] < 0)
    Q = [i for i in range(n) if B0[i] == [rk[i][1]] and rk[i][2] in J0]
    for r in range(len(Q), -1, -1):
        for S in itertools.combinations(Q, r):
            nb = list(base)
            for i in S: nb[rk[i][2]] = i
            nb = tuple(nb)
            B, J, U, NA, F, T = parts(rk, m, nb)
            if any(rk[i][1] in NA for i in S): continue
            res = _owner_test(rk, m, nb, B, J, U, T, U0, allowed)
            if res: return res + (('upgrades', S),)
    return None


def _owner_test(rk, m, base, B, J, U, T, U0, allowed=None):
    n = len(rk)
    A = [x for x in range(n) if not U[x] and B[x] == [rk[x][0]]]
    def threat_free(bundle, owner):
        s = set(bundle)
        return len(s) <= 2 or not any(x != owner and rk[x][1] in s and rk[x][2] in s for x in A)
    slots = []   # (agent, allowed goods)
    for t in T: slots.append((t, set(J)))
    for u in range(n):
        if U0[u]: slots.append((u, set(g for g in J if threat_free(B[u] + [g], u))))
    def matchable(C, o):
        sl = [s for s in slots if s[0] != o]
        match = {}
        def aug(g, seen):
            for k, (a, allowed) in enumerate(sl):
                if g in allowed and k not in seen:
                    seen.add(k)
                    if k not in match or aug(match[k], seen):
                        match[k] = g; return True
            return False
        return all(aug(g, set()) for g in C)
    if (allowed is None or 'none' in allowed) and matchable(J, None): return ('no owner',)
    for o in T + [u for u in range(n) if U[u]]:
        if allowed is not None and o not in allowed: continue
        for r in range(len(J) + 1):
            for C in itertools.combinations(J, r):
                rest = B[o] + [g for g in J if g not in C]
                if threat_free(rest, o) and matchable(C, o): return ('owner', o, C)
    return None


def lb_simple(rk, m, base, upgrades=False):
    """A simple sufficient test (sound by LB+'s Theorem 1' with slots of size one): (optionally LB's maximal upgrades)
    then |J| <= |T| (no owner: every junk good to a different terminal), or an owner o (terminal or pair holder) and a
    hitting set H of {pi_x : x exposed for o} with |H| <= |T| - [o in T], or o holds nothing and |J| <= |T| + 1."""
    if upgrades: base = upgrade(rk, m, base)
    B, J, U, NA, F, T = parts(rk, m, base); S = len(T)
    if len(J) <= S: return ('no owner',)
    for o in T + [i for i in range(len(rk)) if U[i]]:
        if not B[o] and len(J) <= S + 1: return ('owner holding nothing, two goods', o)
        E = exposed(rk, base, o, B, J, U)
        if any({rk[x][1], rk[x][2]} <= set(B[o]) for x in E): continue
        H = min_hit([[g for g in (rk[x][1], rk[x][2]) if g in J] for x in E], S - (1 if o in T else 0))
        if H is not None: return ('owner', o, H)
    return None
