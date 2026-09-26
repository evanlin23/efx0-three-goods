"""LIL (k4/c4min_reduce.md §5.3, #51) with its move catalogue as the text states it, for f = 1 (proof/k4-strategy).
Written from the text, on #51's red_lib (keys, configurations, owner test) via k4/suite/ext.py:
  M1: one free agent y re-pairs inside Q_y ∪ L (any pair whose part in U_y is admissible);
  M4: rotation along a threat cycle of free agents, plain, or with one receiver z of kind (R) (4 goods, holding a rich
      pair without its top a_z, with s_z in the pool) taking {a_z, s_z}, a_z from its predecessor's pair, the other good
      of that pair to the pool (Lemma R (iii));
  M5: #50's path move from a terminal tau along a simple threat path tau -> ... -> p_k threatening x: every p_{i+1}
      takes Q_{p_i}, x takes its BEST admissible pair of (Q_{p_k} ∪ L) ∩ ... (by value), tau takes g (the new key);
      plus at most one Lemma R (iii)-modified receiver as in M4.
#51's red_lil.py (k4/red.c too) implements a broader catalogue: a modified receiver may trade any good of its received
pair for any pool good, and x takes any admissible pair. stuck(prof, key, Q, L, text=True) tests the text catalogue.
The potential is Phi_r = (r', -t, Lam)."""
import itertools, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ext


def kindR(P, K, z, Qz):
    U = [g for g in P.vals[z] if g != K.g]
    if len(U) != 4: return None
    a = max(U, key=lambda g: P.vals[z][g])
    gs = [g for g in RB().bits(Qz)]
    if a in gs or not all((K.U[z] >> g) & 1 for g in gs): return None
    if sum(P.vals[z][g] for g in gs) <= P.vals[z][a]: return None       # a rich pair
    if K.robust(z, Qz): return None
    s = [g for g in U if g != a and g not in gs][0]
    return a, s


def RB(): return ext.red_lib()


def text_moves(P, Ks, K, Q, L):
    B = RB(); x, g = K.x, K.g
    for y in K.free:                                   # M1
        W = list(B.bits(Q[y] | L))
        for a, b in itertools.combinations(W, 2):
            S = (1 << a) | (1 << b)
            if S != Q[y]:
                Q2 = dict(Q); Q2[y] = S; yield K, Q2, (Q[y] | L) & ~S
    thr = {o: [y for y in K.free if y != o and P.threat(y, Q[o] | L, Q[y])] for o in K.free}
    xthr = [o for o in K.free if P.threat(x, Q[o] | L, 1 << g)]
    def modified(base, recv, Lc, Kc):                  # at most one Lemma R (iii) receiver
        yield base, Lc
        for z, S in recv:
            r = kindR(P, K, z, Q[z])
            if not r: continue
            a, s = r
            if (S >> a) & 1 and (Lc >> s) & 1:
                Q3 = dict(base); Q3[z] = (1 << a) | (1 << s)
                yield Q3, (Lc & ~(1 << s)) | (S & ~(1 << a))
    seen = set()                                        # M4
    for s0 in K.free:
        stack = [(s0, [s0])]
        while stack:
            v, path = stack.pop()
            for y in thr[v]:
                if y == s0 and len(path) >= 2 and frozenset(path) not in seen:
                    seen.add(frozenset(path)); k = len(path); Q2 = dict(Q)
                    for j in range(k): Q2[path[(j + 1) % k]] = Q[path[j]]
                    for Q3, L3 in modified(Q2, [(path[(j + 1) % k], Q[path[j]]) for j in range(k)], L, K): yield K, Q3, L3
                elif y not in path and y > s0: stack.append((y, path + [y]))
    def paths(start):                                   # M5
        out = []
        def rec(p):
            if p[-1] in xthr: out.append(list(p))
            for y in thr[p[-1]]:
                if y not in p: rec(p + [y])
        rec([start]); return out
    for tau in K.free:
        if not K.needs_g(tau, Q[tau]) or tau not in Ks: continue
        Kt = Ks[tau]
        for path in paths(tau):
            base = {y: Q[y] for y in K.free if y not in path}
            for i in range(len(path) - 1): base[path[i + 1]] = Q[path[i]]
            W = list(B.bits(Q[path[-1]] | L))
            Ux = Kt.U[x]
            opts = [(1 << a) | (1 << b) for a, b in itertools.combinations(W, 2) if P.admissible(x, ((1 << a) | (1 << b)) & Ux, Ux)]
            if not opts: continue
            bv = max(P.v(x, S) for S in opts)
            for Px in [S for S in opts if P.v(x, S) == bv]:
                Q2 = dict(base); Q2[x] = Px; L2 = (Q[path[-1]] | L) & ~Px
                for Q3, L3 in modified(Q2, [(path[i + 1], Q[path[i]]) for i in range(len(path) - 1)], L2, Kt): yield Kt, Q3, L3


def stuck(sets, vals, key_g, key_x, Q, L, text=True):
    """True if no move of the catalogue gives a configuration with a larger (r', -t, Lam)"""
    os.environ['RFIRST'] = '1'; os.environ.pop('M2', None)
    B, RL = RB(), ext.red_lil()
    m = 1 + max(g for S in sets for g in S)
    P = B.Prof([dict(zip(S, V)) for S, V in zip(sets, vals)], m)
    f, keys = B.fewest_frozen_le1(P)
    assert f == 1 and (key_g, key_x) in keys, (f, keys)
    Ks = {x: B.Key(P, g, x) for g, x in keys}
    K = Ks[key_x]
    Qm = {y: sum(1 << h for h in q) for y, q in Q.items()}; Lm = sum(1 << h for h in L)
    assert RL.is_config(P, K, Qm, Lm)
    compl = any(K.owner_status(Qm, Lm, o)[2] for o in K.free)
    p0 = RL.phi(P, K, Qm, Lm)
    gen = text_moves(P, Ks, K, Qm, Lm) if text else RL.moves(P, Ks, K, Qm, Lm)
    better = [(K2.x, Q2, L2) for K2, Q2, L2 in gen if RL.is_config(P, K2, Q2, L2) and RL.phi(P, K2, Q2, L2) > p0]
    return compl, p0, not better, better[:1]
