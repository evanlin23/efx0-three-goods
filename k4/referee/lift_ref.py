#!/usr/bin/env python3
"""Referee check of the second-move lemmas:
  * Lemma EX* is Lemma M at B' (checked by re-derivation; Lemma M was checked in matching_ref.py);
  * Lemmas LIFT-red and LIFT-1 (k4/matching.md §6, branch proof/k4-matching at 0ee5969);
  * Lemma LIFT (k4/oc1max_multi.md §8, branch proof/k4-oc1max-multi at 0d26500 / 5371d9b).
Own code (cert_ref.py / oc1hall_ref.py helpers), raw EFX0; nothing from k4/matching/ or k4/oc1max_multi/ is run.

Starts: (i) SD picks of random strict instances (<= 4 relevant goods, n = 3..5), kept when perfect; (ii) one-move-
failing perfect starts near the 11 n = 4 OC1^max counterexamples (one or two agents re-drawn with strict core values;
oc_depth = 2 by my own search).

LIFT-red: every P1 (official chain from Y ending at a holder z of Y, agents after the head take no junk, |H0^1| = 2,
H0^1 ⊆ J ∪ {y_z}, z a holder of B1) and every P2 (canonical at B1, ending at z, z's new bundle a single good, head
h != P1's head, H0^2 ⊆ J1 ∪ {a} improving): every junk good of B2 is unwanted; no bundle other than h's threatens
anybody at B2 values; and "X = H0^2 ∪ J2 to h is EFX0 <=> X threatens no i != h at its B2 value".
LIFT-1: when moreover t (z's good at B2) is z's favourite of R_z and (L1)-(L3) hold: h takes X - {g}, z takes {t, g}
(g = z's best good of J2) is EFX0 and S*-shaped. Remarks: (L3) holds for every second sharer off both chains; for P1's
head off P2, (L3) fails only if P1 = (k, z) with y_k ∈ X.
Mutations: 'junkmid' (P1's middle agents may take junk) for LIFT-red; 'nofav' (t need not be z's favourite) for LIFT-1.
LIFT: at B1 after a canonical chain whose head takes a pair T (two junk goods, or a junk good and y_z) and every other
agent with a relevant good values each good of T at most its B1 value: (1) every official move of I- from B1- is an
official move of I from B1; (2) every one-absorber completion of B1- or of a one-move state of I-, in which no bundle
threatens k at v_k(T), lifts (with X_k = T) to a one-absorber EFX0 completion in I. Also the remark: if some bundle
threatens k, it holds {Y_k, l} worth > v_k(T), or k wants l and l is in a bundle of >= 2 goods.
"""
import itertools, random, sys, json
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, efx0, rel, sd, nu, complete, moves, mk, core_values, oc_depth

def threatened(v, i, S, t):
    tot = val(v, i, S)
    return len(S) >= 2 and any(tot - v[i][h] > t for h in S)

def frozen_set(v, B):
    n = len(B)
    return {j for j in range(n) if any(i != j and any(v[i][g] > val(v, i, B[i]) for g in B[j]) for i in range(n))}

def holders(v, B):
    fr = frozen_set(v, B)
    return {j for j in range(len(B)) if len(B[j]) <= 1 and j not in fr}

def subsets(S):
    S = sorted(S)
    for k in range(len(S) + 1):
        for c in itertools.combinations(S, k):
            yield set(c)

def p1_chains(v, Y, J, junkmid=False):
    """official chains from the picks ending at a holder z of Y, |H0| = 2, H0 ⊆ J ∪ {y_z}; middle agents no junk."""
    n = len(Y); R = [rel(v, i) for i in range(n)]
    B = [{y} for y in Y]; p = [v[i][Y[i]] for i in range(n)]
    hold = holders(v, B)
    for t in range(1, n):
        for seq in itertools.permutations(range(n), t + 1):
            z = seq[-1]
            if z not in hold:
                continue
            def rec(i, used, Hs):
                if i > t:
                    for H0 in itertools.combinations(sorted(((J - used) | {Y[z]}) & R[seq[0]]), 2):
                        if val(v, seq[0], H0) > p[seq[0]]:
                            yield seq, Hs, set(H0)
                    return
                xi = seq[i]
                opts = list(subsets((J - used) & R[xi])) if junkmid else [set()]
                for Hi in opts:
                    if val(v, xi, {Y[seq[i - 1]]} | Hi) > p[xi]:
                        yield from rec(i + 1, used | Hi, Hs + [Hi])
            yield from rec(1, set(), [])

def apply_chain(B, seq, Hs, H0):
    c = [set(b) for b in B]
    for i in range(1, len(seq)):
        c[seq[i]] = B[seq[i - 1]] | Hs[i - 1]
    c[seq[0]] = set(H0)
    return c

def canonical_p2(v, B1, J1, z, k):
    """canonical chains at B1 ending at z (each agent after the head takes its predecessor's bundle alone, strict
    gain); z's new bundle a single good; head h != k; H0 ⊆ J1 ∪ B1_z improving for h."""
    n = len(B1); R = [rel(v, i) for i in range(n)]
    pv = [val(v, i, B1[i]) for i in range(n)]
    for t in range(1, n):
        for seq in itertools.permutations(range(n), t + 1):
            if seq[-1] != z or seq[0] == k or any(not B1[x] for x in seq[:-1]):
                continue
            if any(val(v, seq[i], B1[seq[i - 1]]) <= pv[seq[i]] for i in range(1, t + 1)):
                continue
            if len(B1[seq[-2]]) != 1:
                continue
            h = seq[0]
            for H0 in subsets((J1 | B1[z]) & R[h]):
                if H0 and val(v, h, H0) > pv[h]:
                    yield seq, H0

def lift_checks(v, Y, c, ex, tag, mut=None):
    n = len(Y); m = len(v[0])
    J = set(range(m)) - set(Y)
    B = [{y} for y in Y]; p = [v[i][Y[i]] for i in range(n)]
    for seq1, Hs, H01 in p1_chains(v, Y, J, junkmid=(mut == "junkmid")):
        k, z = seq1[0], seq1[-1]
        B1 = apply_chain(B, seq1, Hs, H01)
        if z not in holders(v, B1):
            continue
        J1 = set(range(m)) - set().union(*B1)
        a = next(iter(B1[z]))
        for seq2, H02 in canonical_p2(v, B1, J1, z, k):
            h = seq2[0]
            B2 = [set(b) for b in B1]
            for i in range(1, len(seq2)):
                B2[seq2[i]] = set(B1[seq2[i - 1]])
            B2[h] = set(H02)
            J2 = set(range(m)) - set().union(*B2)
            vb = [val(v, i, B2[i]) for i in range(n)]
            c[tag + "_liftred_pairs"] += 1
            # LIFT-red
            unw = not any(v[i][g] > vb[i] for g in J2 for i in range(n))
            nothr = not any(threatened(v, i, B2[j], vb[i]) for j in range(n) if j != h for i in range(n) if i != j)
            X = H02 | J2
            A = [set(b) for b in B2]; A[h] = set(X)
            iff = efx0(v, A) == (not any(threatened(v, i, X, vb[i]) for i in range(n) if i != h))
            if not (unw and nothr and iff):
                c[tag + "_liftred_fail"] += 1
                if len(ex) < 6:
                    ex.append(("LIFT-red", mut, tag, v, Y, seq1, sorted(H01), seq2, sorted(H02), unw, nothr, iff))
            if mut == "junkmid":
                continue
            # LIFT-1
            (t_,) = B2[z]
            fav = all(v[z][t_] >= v[z][g] for g in rel(v, z))
            L1 = not any(i != z and v[i][t_] > vb[i] for i in range(n))
            Gz = J2 & rel(v, z)
            gbest = max((v[z][x] for x in Gz), default=0)
            L2 = val(v, z, H02 & rel(v, z)) <= v[z][t_] + (0 if mut == "L2strict" else gbest)   # (L2') (83281b6)
            Lb = val(v, z, X & rel(v, z)) <= v[z][t_]                                           # case (b) (7e6cd80)
            if mut == "noL2":
                L2 = True
            L3 = all(len(X & rel(v, i)) <= 1 for i in range(n) if i not in (h, z))
            if L3 and Lb:
                Xb = [set(b) for b in B2]; Xb[h] = set(X)
                c[tag + "_lift1b_tests"] += 1
                if not (efx0(v, Xb) and set().union(*Xb) == set(range(m))):
                    c[tag + "_lift1b_fail"] += 1
                    if len(ex) < 6:
                        ex.append(("LIFT-1b", tag, v, Y, seq1, sorted(H01), seq2, sorted(H02)))
            # remarks
            P = set(seq1) | set(seq2)
            for kp in range(n):
                if kp not in P and val(v, kp, H01) > p[kp]:
                    c[tag + "_sharer_tests"] += 1
                    if len(X & rel(v, kp)) > 1:
                        c[tag + "_sharer_fail"] += 1
            if k not in seq2:
                c[tag + "_headk_tests"] += 1
                if len(X & rel(v, k)) > 1 and not (len(seq1) == 2 and Y[k] in X):
                    c[tag + "_headk_fail"] += 1
            if not (L1 and L2 and L3 and (fav or mut == "nofav")):
                continue
            G = J2 & rel(v, z)
            Xf = [set(b) for b in B2]
            if G:
                g = max(sorted(G), key=lambda x: v[z][x])
                Xf[h] = X - {g}; Xf[z] = {t_, g}
            else:
                Xf[h] = set(X)
            c[tag + "_lift1_tests"] += 1
            shape = all(len(Xf[j] - B2[j]) <= 1 for j in range(n) if j != h) and \
                all(not (Xf[j] - B2[j]) for j in range(n) if j not in (h, z))
            if not (efx0(v, Xf) and shape and set().union(*Xf) == set(range(m))):
                c[tag + "_lift1_fail"] += 1
                if len(ex) < 6:
                    ex.append(("LIFT-1", mut, tag, v, Y, seq1, sorted(H01), seq2, sorted(H02), fav))

def reduced(v, B, k, T):
    n = len(B); m = len(v[0])
    ag = [i for i in range(n) if i != k]; goods = [g for g in range(m) if g not in T]
    vr = [[v[i][g] for g in goods] for i in ag]
    Br = [{goods.index(g) for g in B[i]} for i in ag]
    return vr, Br, ag, goods

def liftback(Cr, ag, goods, k, T, n):
    C = [set() for _ in range(n)]
    for idx, i in enumerate(ag):
        C[i] = {goods[g] for g in Cr[idx]}
    C[k] = set(T)
    return C

def oa_completions(v, B):
    n = len(B); m = len(v[0]); J = sorted(set(range(m)) - set().union(*B))
    for f in itertools.product(range(n), repeat=len(J)):
        cnt = [0] * n
        for x in f:
            cnt[x] += 1
        if sum(1 for x in cnt if x >= 2) > 1:
            continue
        X = [set(b) for b in B]
        for g, x in zip(J, f):
            X[x].add(g)
        if efx0(v, X):
            yield X

def multi_lift(v, Y, c, ex, tag):
    n = len(Y); m = len(v[0])
    J = set(range(m)) - set(Y)
    B = [{y} for y in Y]; p = [v[i][Y[i]] for i in range(n)]
    F = frozen_set(v, B)
    # canonical chains from the picks (x_i wants y_{x_{i-1}}, head unfrozen), head k takes a pair T
    def ext(seq):
        last = seq[-1]
        for w in range(n):
            if w not in seq and v[w][Y[last]] > p[w]:
                if w not in F:
                    yield seq + [w]
                else:
                    yield from ext(seq + [w])
    for k in range(n):
        if k not in F:
            continue
        for seq in ext([k]):
            z = seq[-1]
            for T in itertools.combinations(sorted((J | {Y[z]}) & rel(v, k)), 2):
                T = set(T)
                if not val(v, k, T) > p[k]:
                    continue
                B1 = apply_chain(B, seq, [set()] * (len(seq) - 1), T)
                vb = [val(v, i, B1[i]) for i in range(n)]
                if any(v[i][g] > vb[i] for i in range(n) if i != k for g in T):
                    c[tag + "_lift_hyp_fails"] += 1     # the lemma's hypothesis on T (expected never, by (I2), (U))
                    continue
                c[tag + "_lift_states"] += 1
                vr, Br, ag, goods = reduced(v, B1, k, T)
                full_moves = {tuple(frozenset(b) for b in s) for s in moves(v, B1)}
                Cs = [Br] + moves(vr, Br)
                for ci, Cr in enumerate(Cs):
                    C = liftback(Cr, ag, goods, k, T, n)
                    if ci:
                        c[tag + "_lift_moves"] += 1
                        if tuple(frozenset(b) for b in C) not in full_moves:
                            c[tag + "_lift_item1_fail"] += 1
                            if len(ex) < 6:
                                ex.append(("LIFT-1item", tag, v, Y, seq, sorted(T), ci))
                    for Xr in oa_completions(vr, Cr):
                        Xl = liftback(Xr, ag, goods, k, T, n)
                        thr = any(threatened(v, k, Xl[j], v[k][min(T)] + v[k][max(T)]) for j in range(n) if j != k)
                        # the remark's characterization
                        if thr:
                            ell = [g for g in rel(v, k) if g not in T and g != Y[k]]
                            ok = any((Y[k] in Xl[j] and any(l in Xl[j] for l in ell) and
                                      v[k][Y[k]] + sum(v[k][l] for l in ell if l in Xl[j]) > val(v, k, T)) or
                                     any(l in Xl[j] and len(Xl[j]) >= 2 and v[k][l] > val(v, k, T) for l in ell)
                                     for j in range(n) if j != k)
                            c[tag + "_lift_remark_tests"] += 1
                            if not ok:
                                c[tag + "_lift_remark_fail"] += 1
                            continue
                        c[tag + "_lift_item2_tests"] += 1
                        if not efx0(v, Xl) or sum(1 for i in range(n) if len(Xl[i] - C[i]) >= 2) > 1:
                            c[tag + "_lift_item2_fail"] += 1
                            if len(ex) < 6:
                                ex.append(("LIFT-2item", tag, v, Y, seq, sorted(T)))

def random_instance(rng, n):
    m = rng.randint(n + 2, n + 3)
    v = [[0] * m for _ in range(n)]
    for i in range(n):
        for g, x in zip(rng.sample(range(m), 4), rng.sample(range(1, 40), 4)):
            v[i][g] = x
    return v

def run(N, seed, mut=None, cexfile=None):
    rng = random.Random(seed)
    from collections import Counter
    c = Counter(); ex = []
    insts = []
    if cexfile:
        import ast
        d = json.load(open(cexfile)); insts = d["instances"]
        if isinstance(insts, str):
            insts = ast.literal_eval(insts)
    for it in range(N):
        # (i) random perfect starts
        n = rng.randint(3, 5)
        v = random_instance(rng, n)
        orders = list(itertools.permutations(range(n))); rng.shuffle(orders)
        seen = set()
        for o in orders[:4]:
            Y = sd(v, o)
            if tuple(Y) in seen or any(y is None for y in Y) or len(v[0]) - n > 5:
                continue
            seen.add(tuple(Y)); c["rand_starts"] += 1
            lift_checks(v, Y, c, ex, "rand", mut)
            if mut is None:
                multi_lift(v, Y, c, ex, "rand")
        # (ii) failing starts near the 11 counterexamples
        if insts:
            I = rng.choice(insts); sets = I["sets"]; n = len(sets)
            vals = [list(x) for x in I["vals"]]
            for i in rng.sample(range(n), rng.choice([1, 1, 2])):
                vals[i] = core_values(rng, sets, i)
            v = mk(sets, vals)
            nv = nu(v); seen = set()
            for o in itertools.permutations(range(n)):
                Y = sd(v, o)
                if tuple(Y) in seen or sum(1 for y in Y if y is not None) != nv or any(y is None for y in Y):
                    continue
                seen.add(tuple(Y))
                if oc_depth(v, Y, 1) is None:
                    c["fail_starts"] += 1
                    lift_checks(v, Y, c, ex, "fail", mut)
                    if mut is None:
                        multi_lift(v, Y, c, ex, "fail")
    print(json.dumps(dict(source=f"LIFT-red / LIFT-1 / LIFT N={N} seed={seed} mutation={mut}", **dict(sorted(c.items())))))
    for e in ex[:6]:
        print("EXAMPLE", e)

if __name__ == "__main__":
    N, seed = int(sys.argv[1]), int(sys.argv[2])
    mut = sys.argv[3] if len(sys.argv) > 3 and sys.argv[3] != "none" else None
    cexf = sys.argv[4] if len(sys.argv) > 4 else None
    run(N, seed, mut, cexf)
