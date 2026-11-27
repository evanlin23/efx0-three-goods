"""The matroid-partition form of the one-absorber completion (coordinator's proposal; k4/oc1_hall.md §12).

Fixed start (serial-dictatorship picks) and unfrozen owner o.  Junk goods go to o (the absorber) or to the slots of
the holders N_1 (unfrozen agents other than o), one each; frozen agents take nothing (shape S*).
  * M_T: the transversal matroid on J of the bipartite graph G in which h ~ u (u a holder) iff
      u is unexposed (not threatened by W_o = {Y_o} + J at its pick value), or
      u values h and {Y_u, h} is robust inside R'_u = {Y_u} + (W_o & R_u).
    (Unmatched exposed holders serve themselves by Theorem DT's moves, as in Lemma 2.)
  * For each frozen agent i: D_i = J & R_i (its junk goods), P_i = {Y_o} & R_i (fixed in the absorber's bundle), and
    I_i = {A subset of D_i : v_i(P_i + A) <= p_i}, the sets the absorber may hold (conservative: the strictness clause
    is ignored, i.e. the absorber is assumed to hold a good i does not value).
  * MODEL: some H subset of J is independent in M_T and, for every frozen i, D_i - H is in I_i (brute force over H).
  * MODEL_H: the same, but a holder's admissibility for h is recomputed for each H as in Corollary 2.1 (exposure at
    W_o - H; safe with h rather than robust); not a fixed matroid.
  * MODEL_S: MODEL with the frozen agents' threat computed exactly (strictness clause); MODEL_HS: both changes, which
    is Lemma 2's count and must equal EXACT.
  * RADO: for every S subset of J, sum_i (|S & D_i| - r_i(S & D_i)) <= r_T(S)   (r_i = largest member of I_i inside).
    Edmonds' matroid partition theorem makes RADO equivalent to MODEL when the D_i are pairwise disjoint and every I_i
    is a matroid.
Compared with EXACT (the raw S* enumeration with owner o, ohlib.shaped_completion) and, per start, with the SAT
one-absorber test (k4/sdc/oc_absorb.extends_A, which also allows compensated frozen slots and frozen owners).
Mismatches are classified: overlapping D_i; a frozen agent whose I_i is not a matroid; neither ("other").

    python3 k4/oc1_hall/matroid_check.py SRC
"""
import sys, os, itertools, collections, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, threatened, shaped_completion
from lemma2_true_check import max_matching
from sdclib import Enc
from oc_absorb import extends_A
from min_frozen import load


def is_matroid(ground, indep):
    """indep: predicate on frozensets; checks downward closure and the exchange axiom (tiny ground sets)"""
    fam = [frozenset(A) for r in range(len(ground) + 1) for A in itertools.combinations(ground, r) if indep(frozenset(A))]
    fs = set(fam)
    for A in fam:
        for g in A:
            if A - {g} not in fs: return False
    for A in fam:
        for B in fam:
            if len(A) < len(B) and not any(A | {g} in fs for g in B - A): return False
    return True


def danger_kind(I, i, D, P, p):
    """the minimal dangerous subsets of D (given P fixed), as a sorted tuple of tuples"""
    dang = [frozenset(A) for r in range(len(D) + 1) for A in itertools.combinations(D, r) if I.val(i, list(P) + list(A)) > p]
    mins = [A for A in dang if not any(B < A for B in dang)]
    return mins


def analyse(I, P, o):
    n = I.n; Y = P.Y; J = P.J
    Wo = ([Y[o]] if Y[o] is not None else []) + J
    holders = [u for u in range(n) if u != o and u not in P.F]
    # transversal graph
    adj = {}
    for h in J:
        adj[h] = []
        for u in holders:
            if not threatened(I, u, P.pv[u], Wo): adj[h].append(u); continue
            if h in I.R[u]:
                Rp = [Y[u]] + [g for g in Wo if g in I.R[u]]
                if I.val(u, [Y[u], h]) >= I.val(u, [g for g in Rp if g not in (Y[u], h)]): adj[h].append(u)
    def rT(S):
        # max matching of goods S into holders
        return len(max_matching({h: adj[h] for h in S}, list(S)))
    frozen = [i for i in P.F if i != o]
    D = {i: [g for g in J if g in I.R[i]] for i in frozen}
    Pf = {i: ([Y[o]] if Y[o] is not None and Y[o] in I.R[i] else []) for i in frozen}
    indep = {i: (lambda A, i=i: I.val(i, Pf[i] + list(A)) <= P.pv[i]) for i in frozen}
    def ri(i, T):
        T = list(T)
        for r in range(len(T), -1, -1):
            if any(indep[i](frozenset(A)) for A in itertools.combinations(T, r)): return r
        return 0
    # MODEL by brute force
    model = False
    for r in range(len(J) + 1):
        for H in itertools.combinations(J, r):
            if rT(H) < len(H): continue
            if all(indep[i](frozenset(g for g in D[i] if g not in H)) for i in frozen): model = True; break
        if model: break
    # RADO
    rado = True
    for r in range(1, len(J) + 1):
        for S in itertools.combinations(J, r):
            Ss = set(S)
            lhs = sum(len(Ss & set(D[i])) - ri(i, Ss & set(D[i])) for i in frozen)
            if lhs > rT(S): rado = False; break
        if not rado: break
    # MODEL_H: admissibility recomputed for each H (Corollary 2.1), frozen constraints as in MODEL
    model_h = False
    for r in range(len(J) + 1):
        for H in itertools.combinations(J, r):
            if not all(indep[i](frozenset(g for g in D[i] if g not in H)) for i in frozen): continue
            WH = [g for g in Wo if g not in H]
            exposed = [u for u in holders if threatened(I, u, P.pv[u], WH)]
            ed = {u: [h for h in H if h in I.R[u] and not threatened(I, u, P.pv[u] + I.v[u][h], WH)] for u in exposed}
            if len(H) + len(exposed) - len(max_matching(ed, exposed)) <= len(holders): model_h = True; break
        if model_h: break
    # MODEL_HS: MODEL_H with the frozen agents' threat computed exactly (strictness clause included) = Lemma 2's count
    model_hs = False
    for r in range(len(J) + 1):
        for H in itertools.combinations(J, r):
            WH = [g for g in Wo if g not in H]
            if any(threatened(I, i, P.pv[i], WH) for i in frozen): continue
            exposed = [u for u in holders if threatened(I, u, P.pv[u], WH)]
            ed = {u: [h for h in H if h in I.R[u] and not threatened(I, u, P.pv[u] + I.v[u][h], WH)] for u in exposed}
            if len(H) + len(exposed) - len(max_matching(ed, exposed)) <= len(holders): model_hs = True; break
        if model_hs: break
    # MODEL_S: MODEL (fixed transversal graph) with the exact frozen threat
    model_s = False
    for r in range(len(J) + 1):
        for H in itertools.combinations(J, r):
            if rT(H) < len(H): continue
            WH = [g for g in Wo if g not in H]
            if not any(threatened(I, i, P.pv[i], WH) for i in frozen): model_s = True; break
        if model_s: break
    overlap = any(set(D[i]) & set(D[j]) for i, j in itertools.combinations(frozen, 2))
    nonmat = [i for i in frozen if not is_matroid(D[i], indep[i])]
    kinds = [tuple(sorted(tuple(sorted(I.key[i][g] for g in A)) for A in danger_kind(I, i, D[i], Pf[i], P.pv[i]))) for i in nonmat]
    return model, rado, overlap, nonmat, holders, model_h, kinds, model_hs, model_s


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/oc1_hall/matroid_check.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > 5: continue
        I = Inst(sets, vals, m, name); E = Enc(sets, vals, m); seen = set()
        for od in itertools.permutations(range(n)):
            Y = picks(I, od)
            if Y in seen: continue
            seen.add(Y); P = Picks(I, Y); base = base_of_picks(I, Y)
            sat = extends_A(E, base, 1)
            anymodel = anyrado = anyexact = False
            for o in range(n):
                if o in P.F: continue
                model, rado, overlap, nonmat, holders, model_h, kinds, model_hs, model_s = analyse(I, P, o)
                exact = shaped_completion(I, base, o, holders)
                anymodel |= model; anyrado |= rado; anyexact |= exact
                cls = 'overlapping D_i' if overlap else ('non-matroid agent' if nonmat else 'disjoint, all matroids')
                C['owner tests'] += 1; C['owner tests: ' + cls] += 1
                if model and not exact: C['MODEL YES BUT EXACT NO (bug)'] += 1; print('BUG', name, Y, o, flush=True)
                if model != rado:
                    C['  RADO != MODEL, ' + cls] += 1
                    if cls == 'disjoint, all matroids':
                        print('RADO/MODEL DISAGREE ON DISJOINT MATROIDS', name, json.dumps((sets, vals)), Y, o, model, rado, flush=True)
                if exact != rado: C['  RADO != EXACT, ' + cls] += 1
                if exact != model: C['  MODEL != EXACT (model too conservative), ' + cls] += 1
                if exact != model_h: C['  MODEL_H (admissibility per H) != EXACT, ' + cls] += 1
                if exact != model_hs: C['  MODEL_HS (per-H admissibility, exact frozen threat) != EXACT, ' + cls] += 1
                if exact != model_s: C['  MODEL_S (fixed graph, exact frozen threat) != EXACT, ' + cls] += 1
                if nonmat:
                    C['  owner tests with a non-matroid frozen agent'] += 1
                    for k in kinds: C['    non-matroid danger family (ranks of goods) %s' % (k,)] += 1
            C['starts'] += 1
            C['starts: SAT %s, EXACT(S*, unfrozen owner) %s, RADO %s' % (sat, anyexact, anyrado)] += 1
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
