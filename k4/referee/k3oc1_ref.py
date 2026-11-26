#!/usr/bin/env python3
"""Referee check of Theorem R1C (k4/k3_oc1.md §3, branch claude/k4-k3-oc1), written independently.

Setting (k3_oc1.md §1): every agent values exactly three goods a > b > c, strictly balanced (values 4, 3, 2 are exact
by L5); goods nobody values are allowed.

For every order pi of an instance:
  * draft = serial dictatorship of pi;
  * R1-compatible: some order sigma gives the same picks and obeys R1 priority (whenever an unprocessed agent has
    lost a good, the next agent is one such agent);
  * for every R1-compatible sigma: LB+ (proofs/lb_last_step.md, read as text) with every cap equal to one:
    upgrades (smallest index first), owner r = last agent of sigma not upgraded; if r fails Lemma 1, assert the bad
    case of Theorem A and rotate along every need chain from k* (leader of sigma's last block) to r; build the
    completion of Lemma 1 (owner r or k, or no owner) and check it against the raw EFX0 definition and the
    one-absorber condition (at most one agent receives two or more goods outside its base);
  * independently: brute-force OC1 (one-absorber completion of the picks, or after one improving chain of k4/sdc.md
    §29, any chain) from the raw definition.
Shares no code with k4/k3oc1/.
"""
import itertools, random, sys, json

VAL = (4, 3, 2)

def make_vals(n, m, rk):
    v = [[0] * m for _ in range(n)]
    for i in range(n):
        for g, x in zip(rk[i], VAL):
            v[i][g] = x
    return v

def efx0(v, X):
    n = len(X)
    for i in range(n):
        vi = sum(v[i][g] for g in X[i])
        for j in range(n):
            if i != j and len(X[j]) >= 2:
                tot = sum(v[i][g] for g in X[j])
                if any(tot - v[i][g] > vi for g in X[j]):
                    return False
    return True

def draft(rk, order, m):
    G = set(range(m)); Y = {}
    for i in order:
        p = next((g for g in rk[i] if g in G), None)
        Y[i] = p
        if p is not None:
            G.discard(p)
    return Y

def r1_ok(rk, sigma, m):
    """sigma obeys R1 priority (every agent values exactly three goods)."""
    G = set(range(m)); done = set()
    for i in sigma:
        lost = [x for x in range(len(rk)) if x not in done and len(set(rk[x]) & G) <= 2]
        if lost and i not in lost:
            return False
        p = next((g for g in rk[i] if g in G), None)
        if p is not None:
            G.discard(p)
        done.add(i)
    return True

def blocks(rk, sigma, m):
    """return list of blocks (lists of agents) of an R1-priority run; leader first."""
    G = set(range(m)); B = []
    for i in sigma:
        if set(rk[i]) <= G:
            B.append([i])
        else:
            B[-1].append(i)
        p = next((g for g in rk[i] if g in G), None)
        if p is not None:
            G.discard(p)
    return B

def one_absorber_completions(v, base, m, first_only=True):
    """bases: list of sets. Yield complete EFX0 allocations keeping every base, at most one agent with >= 2 junk."""
    n = len(base)
    held = set().union(*base)
    J = [g for g in range(m) if g not in held]
    for f in itertools.product(range(n), repeat=len(J)):
        cnt = [0] * n
        for a in f:
            cnt[a] += 1
        if sum(1 for c in cnt if c >= 2) > 1:
            continue
        X = [set(b) for b in base]
        for g, a in zip(J, f):
            X[a].add(g)
        if efx0(v, X):
            yield X
            if first_only:
                return

def has_oc(v, base, m):
    return next(one_absorber_completions(v, base, m), None) is not None

def chains(v, rk, base, m):
    """all improving chains of k4/sdc.md §29 from bases `base`; yields new bases."""
    n = len(base)
    held = set().union(*base)
    J = set(range(m)) - held
    R = [set(r) for r in rk]
    def val(i, S):
        return sum(v[i][g] for g in S)
    def subsets(S):
        S = sorted(S)
        for k in range(len(S) + 1):
            for c in itertools.combinations(S, k):
                yield set(c)
    for t in range(1, n):
        for seq in itertools.permutations(range(n), t + 1):
            x0, xt = seq[0], seq[-1]
            # middle and end receivers: x_i takes B_{x_{i-1}} plus H_i subset of J
            def rec(i, usedJ, newb):
                if i > t:
                    # H0 from (J - usedJ) | B_xt, within R_x0
                    pool = ((J - usedJ) | base[xt]) & R[x0]
                    for H0 in subsets(pool):
                        if H0 and val(x0, H0) > val(x0, base[x0]):
                            nb = list(newb)
                            nb[x0] = set(H0)
                            yield nb
                    return
                xi, prev = seq[i], seq[i - 1]
                for Hi in subsets((J - usedJ) & R[xi]):
                    if val(xi, base[prev] | Hi) > val(xi, base[xi]):
                        nb = list(newb); nb[xi] = base[prev] | Hi
                        yield from rec(i + 1, usedJ | Hi, nb)
            yield from rec(1, set(), [set(b) for b in base])

class St:
    def __init__(s):
        s.starts = 0; s.r1c = 0; s.r1c_sigmas = 0; s.extend = 0; s.owner_r = 0; s.no_owner = 0; s.rot = 0
        s.fail = 0; s.badcase_violation = 0; s.oc1_fail = 0; s.oc1_onechain = 0; s.ex = []; s.notr1 = 0
        s.rot_ring = 0; s.rot_chain = 0

def lbplus_unit(v, rk, sigma, m, st, inst):
    n = len(rk)
    a = [r[0] for r in rk]; b = [r[1] for r in rk]; c = [r[2] for r in rk]
    Y = draft(rk, sigma, m)
    picks = {g for g in Y.values() if g is not None}
    U = set(); cu = {}
    def needs(i, Yd):
        if Yd[i] is None:
            return set(rk[i])
        return set(rk[i][:rk[i].index(Yd[i])])
    def state(Yd, U):
        held = {g for g in Yd.values() if g is not None} | {c[u] for u in U}
        J = set(range(m)) - held
        NA = set().union(*[needs(i, Yd) for i in range(n) if i not in U]) if n else set()
        F = {i for i in range(n) if i not in U and Yd[i] is not None and Yd[i] in NA}
        T = [i for i in range(n) if i not in U and i not in F]
        return J, NA, F, T
    # upgrades, smallest index first
    while True:
        J, NA, F, T = state(Y, U)
        k = next((k for k in range(n) if k not in U and Y[k] == b[k] and c[k] in J and b[k] not in NA), None)
        if k is None:
            break
        U.add(k)
    J, NA, F, T = state(Y, U)
    def base_of(i, Yd, U):
        if i in U:
            return {Yd[i], c[i]}
        return {Yd[i]} if Yd[i] is not None else set()
    def exposed(o, Yd, U, J):
        bo = base_of(o, Yd, U)
        return [x for x in range(n) if x not in U and x != o and Yd[x] == a[x] and {b[x], c[x]} <= (J | bo)]
    def try_owner(o, Yd, U):
        J, NA, F, T = state(Yd, U)
        bo = base_of(o, Yd, U)
        E = exposed(o, Yd, U, J)
        if any({b[x], c[x]} <= bo for x in E):
            return None
        slots = [t for t in T if t != o]
        need = len(slots)
        for hs in range(0, need + 1):
            for H in itertools.combinations(sorted(J), hs):
                if all({b[x], c[x]} & set(H) for x in E):
                    # build C ⊇ H of size min(need, |J|)
                    rest = sorted(J - set(H))
                    C = list(H) + rest[:max(0, min(need, len(J)) - len(H))]
                    X = [set(base_of(i, Yd, U)) for i in range(n)]
                    for g, t in zip(C, slots):
                        X[t].add(g)
                    for g in J - set(C):
                        X[o].add(g)
                    return X
        return None
    def no_owner(Yd, U):
        J, NA, F, T = state(Yd, U)
        if len(J) > len(T):
            return None
        X = [set(base_of(i, Yd, U)) for i in range(n)]
        for g, t in zip(sorted(J), T):
            X[t].add(g)
        return X
    def check(X, bases, tag):
        jcnt = sum(1 for i in range(n) if len(X[i] - bases[i]) >= 2)
        ok = efx0(v, X) and jcnt <= 1 and sorted(g for B in X for g in B) == list(range(m))
        if not ok:
            st.fail += 1
            if len(st.ex) < 6:
                st.ex.append((tag, inst, sigma, [sorted(x) for x in X]))
        return ok
    pick_bases = [({Y[i]} if Y[i] is not None else set()) for i in range(n)]
    X = no_owner(Y, U)
    if X is not None:
        st.no_owner += 1; check(X, pick_bases, "no_owner"); return
    order_pos = {i: p for p, i in enumerate(sigma)}
    r = max((i for i in range(n) if i not in U), key=lambda i: order_pos[i])
    X = try_owner(r, Y, U)
    if X is not None:
        st.owner_r += 1; check(X, pick_bases, "owner_r"); return
    # bad case
    B = blocks(rk, sigma, m); Bs = B[-1]; kst = Bs[0]
    E = exposed(r, Y, U, J)
    ok_bad = ([x for x in E if x in Bs] == [kst]) and kst != r and kst in F
    # need chains from k*
    def need_chains(x, path):
        if x in T:
            yield path; return
        for j in range(n):
            if j not in U and j not in path and Y[x] in needs(j, Y):
                yield from need_chains(j, path + [j])
    chs = list(need_chains(kst, [kst])) if kst in F else []
    if not chs or any(ch[-1] != r for ch in chs):
        ok_bad = False
    pis = [frozenset({b[x], c[x]} & J) for x in E]
    if any(p & q for p, q in itertools.combinations(pis, 2)):
        ok_bad = False
    if not ok_bad:
        st.badcase_violation += 1
        if len(st.ex) < 6:
            st.ex.append(("badcase", inst, sigma))
        return
    st.rot += 1
    for ch in chs:
        Y2 = dict(Y)
        for i in range(1, len(ch)):
            Y2[ch[i]] = Y[ch[i - 1]]
        Y2[kst] = b[kst]; U2 = U | {kst}
        if Y[r] in (b[kst], c[kst]):
            st.rot_ring += 1
        else:
            st.rot_chain += 1
        # the bases after the chain (OC1's sense): k* holds {b,c}; others their (shifted) picks
        nb = [({Y2[i]} if Y2[i] is not None else set()) for i in range(n)]
        nb[kst] = {b[kst], c[kst]}
        # improving-chain conditions (strict gains)
        good = sum(v[kst][g] for g in nb[kst]) > v[kst][a[kst]] and all(
            v[ch[i]][Y[ch[i - 1]]] > (v[ch[i]][Y[ch[i]]] if Y[ch[i]] is not None else 0) for i in range(1, len(ch)))
        if not good:
            st.fail += 1
        if Y[r] is not None and Y[r] not in nb[kst]:
            nb[r] = {Y2[r]}  # r took its predecessor's pick; its old pick is released
        X = no_owner(Y2, U2)
        if X is None:
            X = try_owner(kst, Y2, U2)
        if X is None:
            st.fail += 1
            if len(st.ex) < 6:
                st.ex.append(("rot_no_owner", inst, sigma, ch))
        else:
            check(X, nb, "rot")

def oc1_brute(v, rk, Y, m, st, inst, order):
    n = len(rk)
    base = [({Y[i]} if Y[i] is not None else set()) for i in range(n)]
    if has_oc(v, base, m):
        return 0
    for nb in chains(v, rk, base, m):
        if has_oc(v, nb, m):
            st.oc1_onechain += 1
            return 1
    st.oc1_fail += 1
    if len(st.ex) < 6:
        st.ex.append(("oc1_fail", inst, order))
    return 2

def run_instance(rk, m, st, do_oc1=True):
    n = len(rk)
    v = make_vals(n, m, rk)
    seen = {}
    perms = list(itertools.permutations(range(n)))
    # precompute for every sigma its picks and R1 status
    info = []
    for s in perms:
        Y = draft(rk, s, m)
        info.append((s, tuple(Y[i] for i in range(n)), r1_ok(rk, s, m)))
    by_picks = {}
    for s, p, ok in info:
        by_picks.setdefault(p, []).append((s, ok))
    # distinct drafts (every order pi with the same picks has the same OC1 question)
    for p, lst in by_picks.items():
        st.starts += 1
        sigmas = [s for s, ok in lst if ok]
        if do_oc1:
            oc1_brute(v, rk, dict(enumerate(p)), m, st, rk, lst[0][0])
        if not sigmas:
            st.notr1 += 1
            continue
        st.r1c += 1
        for s in sigmas:
            st.r1c_sigmas += 1
            lbplus_unit(v, rk, s, m, st, rk)

def rand_rk(rng, n, m):
    return [rng.sample(range(m), 3) for _ in range(n)]

def out(name, st):
    d = dict(source=name, distinct_drafts=st.starts, r1_compatible=st.r1c, r1_sigmas=st.r1c_sigmas, not_r1=st.notr1,
             no_owner=st.no_owner, owner_r=st.owner_r, rotations=st.rot, rot_chain=st.rot_chain,
             rot_ring=st.rot_ring, failures=st.fail, badcase_violations=st.badcase_violation,
             oc1_one_chain=st.oc1_onechain, oc1_fail=st.oc1_fail)
    print(json.dumps(d)); sys.stdout.flush()
    for e in st.ex:
        print("EXAMPLE", e)

if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "exh3":
        m = int(sys.argv[2]); st = St()
        trip = list(itertools.permutations(range(m), 3))
        # agent 0's triple fixed up to relabelling: (0,1,2)
        for t1 in trip:
            for t2 in trip:
                run_instance([(0, 1, 2), t1, t2], m, st, do_oc1=(len(sys.argv) > 3))
        out(f"exhaustive n=3 m={m} (agent 0 ranks 0>1>2)", st)
    elif mode == "rand":
        N, n, mlo, mhi, seed = map(int, sys.argv[2:7]); oc = len(sys.argv) > 7
        rng = random.Random(seed); st = St()
        for _ in range(N):
            m = rng.randint(mlo, mhi)
            run_instance(rand_rk(rng, n, m), m, st, do_oc1=oc)
        out(f"random N={N} n={n} m={mlo}..{mhi} seed={seed} oc1={oc}", st)


# ---------------------------------------------------------------- Theorem B* (k3_oc1.md §3) and Lemmas 1, 3 (§2)

def pre_state(rk, Y, U, m):
    """J, NA, F, T of a pre-allocation (picks Y, upgraded set U)."""
    n = len(rk)
    c = [r[2] for r in rk]
    held = {g for g in Y.values() if g is not None} | {c[u] for u in U}
    J = set(range(m)) - held
    def needs(i):
        if Y[i] is None:
            return set(rk[i])
        return set(rk[i][:rk[i].index(Y[i])])
    NA = set()
    for i in range(n):
        if i not in U:
            NA |= needs(i)
    F = {i for i in range(n) if i not in U and Y[i] is not None and Y[i] in NA}
    T = [i for i in range(n) if i not in U and i not in F]
    return J, NA, F, T, needs

def min_hit(sets, pool):
    pool = sorted(pool)
    for k in range(len(pool) + 1):
        for H in itertools.combinations(pool, k):
            if all(s & set(H) for s in sets):
                return set(H)
    return None

class BS:
    def __init__(s):
        s.drafts = 0; s.applies = 0; s.rotations = 0; s.fail = 0; s.ex = []; s.chain_not_improving = 0

def bstar_draft(v, rk, Y, m, bs, inst):
    n = len(rk)
    a = [r[0] for r in rk]; b = [r[1] for r in rk]; c = [r[2] for r in rk]
    U = set()
    while True:
        J, NA, F, T, needs = pre_state(rk, Y, U, m)
        k = next((k for k in range(n) if k not in U and Y[k] == b[k] and c[k] in J and b[k] not in NA), None)
        if k is None:
            break
        U.add(k)
    J, NA, F, T, needs = pre_state(rk, Y, U, m)
    bs.drafts += 1
    def E_of(o):
        bo = {Y[o]} if Y[o] is not None else set()
        return [x for x in range(n) if x not in U and x != o and Y[x] == a[x] and {b[x], c[x]} <= (J | bo)]
    def chains_from(x, path, t):
        if x == t:
            yield path; return
        if x not in F:
            return
        for j in range(n):
            if j not in U and j not in path and Y[x] in needs(j):
                yield from chains_from(j, path + [j], t)
    for t in T:
        E = E_of(t)
        sets = [{b[x], c[x]} & J for x in E]
        h = min_hit(sets, J)
        if h is None or len(h) != len(T):   # deficit one for owner t (Lemma 1 needs <= |T| - 1)
            continue
        for k in E:
            if k not in F:
                continue
            pk = {b[k], c[k]}
            if any({b[x], c[x]} == pk for x in E if x != k):
                continue
            rest = [({b[x], c[x]} - pk) for x in E if x != k]
            H4 = min_hit(rest, set().union(*rest) if rest else set())
            if H4 is None or len(H4) > len(T) - 1:
                continue
            chs = [ch for ch in chains_from(k, [k], t) if len(ch) >= 2]
            if not chs:
                continue
            bs.applies += 1
            for ch in chs:
                bs.rotations += 1
                Y2 = dict(Y)
                for i in range(1, len(ch)):
                    Y2[ch[i]] = Y[ch[i - 1]]
                Y2[k] = b[k]; U2 = U | {k}
                J2, NA2, F2, T2, needs2 = pre_state(rk, Y2, U2, m)
                base = [({Y2[i]} if Y2[i] is not None else set()) for i in range(n)]
                for u in U2:
                    base[u] = {Y2[u], c[u]}
                if len(J2) <= len(T2):
                    X = [set(x) for x in base]
                    for g, tt in zip(sorted(J2), T2):
                        X[tt].add(g)
                else:
                    E2 = [x for x in range(n) if x not in U2 and x != k and Y2[x] == a[x] and {b[x], c[x]} <= (J2 | pk)]
                    H = min_hit([{b[x], c[x]} & J2 for x in E2], J2)
                    if H is None or len(H) > len(T2) or any({b[x], c[x]} <= pk for x in E2):
                        bs.fail += 1
                        if len(bs.ex) < 5:
                            bs.ex.append(("owner_k_fails", inst, Y, ch)); continue
                        continue
                    restJ = sorted(J2 - H)
                    C = sorted(H) + restJ[:len(T2) - len(H)]
                    X = [set(x) for x in base]
                    for g, tt in zip(C, T2):
                        X[tt].add(g)
                    X[k] |= J2 - set(C)
                # one-absorber relative to the bases after the chain (k* holds {b,c}; upgraded agents' c is junk)
                nb = [({Y2[i]} if Y2[i] is not None else set()) for i in range(n)]
                nb[k] = set(pk)
                jc = sum(1 for i in range(n) if len(X[i] - nb[i]) >= 2)
                if not (efx0(v, X) and jc <= 1 and sorted(g for x in X for g in x) == list(range(m))):
                    bs.fail += 1
                    if len(bs.ex) < 5:
                        bs.ex.append(("completion_not_efx0", inst, Y, ch, [sorted(x) for x in X]))

def bstar_run(N, n, mlo, mhi, seed):
    rng = random.Random(seed); bs = BS()
    for _ in range(N):
        m = rng.randint(mlo, mhi)
        rk = rand_rk(rng, n, m); v = make_vals(n, m, rk)
        seen = set()
        for pi in itertools.permutations(range(n)):
            Y = draft(rk, pi, m)
            key = tuple(Y[i] for i in range(n))
            if key in seen:
                continue
            seen.add(key)
            bstar_draft(v, rk, Y, m, bs, rk)
    print(json.dumps(dict(source=f"B* random N={N} n={n} m={mlo}..{mhi} seed={seed}", drafts=bs.drafts,
                          bstar_applies=bs.applies, rotations=bs.rotations, failures=bs.fail)))
    for e in bs.ex:
        print("EXAMPLE", e)

# Lemmas 1 and 3 on random valid DE states (pair holders allowed)
def de_states(rng, rk, m, tries):
    n = len(rk)
    for _ in range(tries):
        hold = []; used = set(); ok = True
        for i in range(n):
            opts = [()] + [(g,) for g in rk[i]] + [(rk[i][1], rk[i][2])]
            rng.shuffle(opts)
            h = next((o for o in opts if not (set(o) & used)), ())
            hold.append(set(h)); used |= set(h)
        U = {i for i in range(n) if len(hold[i]) == 2}
        # validity: every wanted good held alone
        wanted = set()
        for i in range(n):
            if i in U:
                continue
            if not hold[i]:
                wanted |= set(rk[i])
            else:
                y = next(iter(hold[i])); wanted |= set(rk[i][:rk[i].index(y)])
        alone = {next(iter(h)) for h in hold if len(h) == 1}
        if wanted <= alone:
            yield hold, U, wanted

def lemma13_run(N, n, mlo, mhi, seed):
    rng = random.Random(seed)
    cnt = dict(states=0, a=0, b=0, c=0, fail=0, lemma3_hyp=0, lemma3_false=0, lemma3_false_pair_in_owner=0, lemma3_general_hyp=0, lemma3_general_false=0)
    ex = []
    for _ in range(N):
        m = rng.randint(mlo, mhi); rk = rand_rk(rng, n, m); v = make_vals(n, m, rk)
        a = [r[0] for r in rk]; b = [r[1] for r in rk]; c = [r[2] for r in rk]
        for hold, U, wanted in de_states(rng, rk, m, 30):
            cnt["states"] += 1
            held = set().union(*hold); J = set(range(m)) - held
            T = [i for i in range(n) if i not in U and not (hold[i] & wanted)]
            Fz = [i for i in range(n) if i not in U and (hold[i] & wanted)]
            def E_of(o):
                return [x for x in range(n) if x not in U and x != o and hold[x] == {a[x]} and {b[x], c[x]} <= (J | hold[o])]
            def build(owner, H):
                X = [set(h) for h in hold]
                slots = [t for t in T if t != owner]
                restJ = sorted(J - H)
                C = sorted(H) + restJ[:max(0, len(slots) - len(H))]
                if len(C) > len(slots):
                    return None
                for g, t in zip(C, slots):
                    X[t].add(g)
                if owner is not None:
                    X[owner] |= J - set(C)
                elif set(C) != J:
                    return None
                return X
            def verify(X, tag):
                jc = sum(1 for i in range(n) if len(X[i] - hold[i]) >= 2)
                if not (efx0(v, X) and jc <= 1):
                    cnt["fail"] += 1
                    if len(ex) < 5:
                        ex.append((tag, rk, [sorted(h) for h in hold], [sorted(x) for x in X]))
            if len(J) <= len(T):
                cnt["a"] += 1; verify(build(None, set()), "a")
            for o in T + sorted(U):
                E = E_of(o)
                if any({b[x], c[x]} <= hold[o] for x in E):
                    cond1 = False
                else:
                    cond1 = True
                H = min_hit([{b[x], c[x]} & J for x in E], J) if cond1 else None
                bok = cond1 and H is not None and len(H) <= len(T) - (1 if o in T else 0)
                if bok:
                    cnt["b"] += 1; X = build(o, H)
                    if X is not None:
                        verify(X, "b")
                # Lemma 3 literal: every exposed agent a terminal => (b) holds for o
                if all(x in T for x in E):
                    cnt["lemma3_hyp"] += 1
                    if not bok:
                        cnt["lemma3_false"] += 1
                        if o in U and not cond1:
                            cnt["lemma3_false_pair_in_owner"] += 1
                        if len(ex) < 5:
                            ex.append(("lemma3_literal_false", rk, [sorted(h) for h in hold], o, E))
                # Lemma 3 general form, with the missing condition added (corrected statement)
                EF = [x for x in E if x not in T]
                hF = min_hit([{b[x], c[x]} & J for x in EF], J)
                if cond1 and hF is not None and len(hF) <= len([t for t in T if t not in E]) - (1 if o in T else 0):
                    cnt["lemma3_general_hyp"] += 1
                    if not bok:
                        cnt["lemma3_general_false"] += 1
            for o in T:
                if not hold[o] and len(J) <= len(T) + 1:
                    cnt["c"] += 1
                    X = [set(h) for h in hold]; Js = sorted(J); others = [t for t in T if t != o]
                    X[o] |= set(Js[:2]); 
                    for g, t in zip(Js[2:], others):
                        X[t].add(g)
                    if len(Js[2:]) <= len(others):
                        verify(X, "c")
    print(json.dumps(dict(source=f"Lemmas 1,3 random DE states N={N} n={n} m={mlo}..{mhi} seed={seed}", **cnt)))
    for e in ex:
        print("EXAMPLE", e)

if __name__ == "__main__" and sys.argv[1] in ("bstar", "lem13"):
    args = list(map(int, sys.argv[2:7]))
    (bstar_run if sys.argv[1] == "bstar" else lemma13_run)(*args)
