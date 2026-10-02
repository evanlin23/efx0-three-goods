#!/usr/bin/env python3
"""Second implementation of the Theorem ZMOVE check (workstream compute/k4-zmove), for k4/zmove_check.py --indep.
EVIDENCE tooling.

Shares no code with k4/zmove_check.py, k4/suite/model.py, k4/dl2_classify.py, PR #80's or PR #82's tools. The
pre-allocations, the min-frozen class, the needs, NA, the frozen agents and the removal-only deficits are those of
k4/rt4_n5_indep.py (the PR #86 auditor's repo-free implementation, on main); everything else is written here from the
statements:
  - the key of a min-frozen P: (frozen agent -> its good); def*(κ) = least deficit over the min-frozen P of key κ;
  - the configurations at κ (k4/sx.md §1, §6): every free agent y holds a 2-subset Q_y of M ∖ 𝒩 (𝒩 = the key's goods),
    disjoint, whose part H_y = Q_y ∩ U_y (U_y = R_y ∖ 𝒩) is admissible: |H_y| <= 2, H_y ≠ ∅ unless U_y = ∅, and every
    good of U_y ∖ H_y is worth less to y than H_y;
  - the Z′-maxima (k4/sx.md §2): lexicographic maxima of (r′, Λ′), r′ = #{free y : v_y(Q_y) >= v_y(U_y ∖ Q_y)},
    Λ′ = Σ_y #{T ⊆ R_y : v_y(T) < v_y(H_y)}; also with T ⊆ U_y (margin_U); P_Q = frozen w on {φ(w)}, free y on H_y;
  - (T3⁺) between two min-frozen states, clause by clause from main's lean/EFX/MovesC.lean MoveT3plus: NA′ = NA; some x
    frozen in P and free in P′; some z free in P and frozen in P′ with B′_z = {g}, g ∈ N_z(B_z); the changed agents
    free in P and in P′ are at most one, and each gives up a good of its base; every other changed agent is frozen in
    P and in P′ (the set W); {B′_i : i ∈ W ∪ {z}} = {B_i : i ∈ W ∪ {x}} as sets of bases. Found by testing every
    min-frozen P′ against the predicate (no move generation);
  - (T4): every changed agent frozen in P and in P′, NA′ = NA; a key edge needs a P′ of another key.
zmove(sets, vals, m) returns f and per key: def*, the number of configurations, the P_Q of the maxima, the margin
(min over maxima of the least def(P′) over the (T3⁺) moves from P_Q), the best per distinct P_Q, nrep (the number of
(T3⁺) targets with def <= 0 summed over the distinct P_Q), margin_U, and whether a (T4) edge to a key of smaller def*
exists.
usage: python3 k4/zmove_indep.py '{"sets": ..., "vals": ..., "m": ...}'      (prints the per-key verdicts)"""
import itertools, json, os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rt4_n5_indep


def zmove(sets, vals, m=None):
    ns = rt4_n5_indep.analyse(sets, vals, m)
    n, m, mf, D, info = ns['n'], ns['m'], ns['mf'], ns['D'], ns['info']
    v = [dict(zip(S, V)) for S, V in zip(sets, vals)]
    val = lambda i, B: sum(v[i].get(g, 0) for g in B)
    INFO = {P: info(P) for P in mf}

    def key(P):
        fz = INFO[P][3]
        return tuple(next(iter(P[i])) if fz[i] else None for i in range(n))
    K = {}
    for P in mf: K.setdefault(key(P), []).append(P)
    dstar = {k: min(D[P] for P in Ps) for k, Ps in K.items()}
    byNA = {}
    for P in mf: byNA.setdefault(INFO[P][1], []).append(P)

    def t3plus(P, P2):
        N1, NA1, J1, f1 = INFO[P]; N2, NA2, J2, f2 = INFO[P2]
        if NA1 != NA2: return False
        ch = [i for i in range(n) if P[i] != P2[i]]
        X = [i for i in ch if f1[i] and not f2[i]]
        Z = [i for i in ch if not f1[i] and f2[i]]
        Y = [i for i in ch if not f1[i] and not f2[i]]
        W = [i for i in ch if f1[i] and f2[i]]
        if len(X) != 1 or len(Z) != 1 or len(Y) > 1: return False
        if any(not (P[h] - P2[h]) for h in Y): return False
        x, z = X[0], Z[0]
        if len(P2[z]) != 1 or not P2[z] <= N1[z]: return False
        return set(P2[i] for i in W + [z]) == set(P[i] for i in W + [x])

    def t4(P, P2):
        N1, NA1, J1, f1 = INFO[P]; N2, NA2, J2, f2 = INFO[P2]
        if NA1 != NA2: return False
        return all(f1[i] and f2[i] for i in range(n) if P[i] != P2[i])

    def best(P):
        """(least def over the (T3⁺) targets of P, the number of targets with def <= 0)"""
        b = float('inf'); nrep = 0
        for P2 in byNA[INFO[P][1]]:
            if P2 != P and (D[P2] < b or D[P2] <= 0) and t3plus(P, P2):
                b = min(b, D[P2]); nrep += D[P2] <= 0
        return b, nrep

    def lev(y, S, pool):
        s = val(y, S)
        return sum(1 for r in range(len(pool) + 1) for T in itertools.combinations(pool, r) if val(y, T) < s)

    def admissible(y, A, U):
        if len(A) > 2 or not A <= U: return False
        if not A: return not U
        a = val(y, A)
        return all(v[y][g] < a for g in U - A)

    out = {}
    for k, Ps in K.items():
        rec = {'dstar': dstar[k]}
        out[k] = rec
        if dstar[k] <= 0: continue
        Nset = frozenset(g for g in k if g is not None)
        Mp = [g for g in range(m) if g not in Nset]
        free = [i for i in range(n) if k[i] is None]
        U = {y: frozenset(sets[y]) - Nset for y in free}
        pairs = {y: [frozenset(c) for c in itertools.combinations(Mp, 2) if admissible(y, frozenset(c) & U[y], U[y])]
                 for y in free}
        confs = []

        def rec_c(j, used, cur):
            if j == len(free):
                confs.append(dict(cur)); return
            y = free[j]
            for Qy in pairs[y]:
                if Qy & used: continue
                cur[y] = Qy; rec_c(j + 1, used | Qy, cur)
            cur.pop(y, None)
        rec_c(0, frozenset(), {})
        assert confs, ('no configuration at a key', k)
        scored = []
        for Q in confs:
            r = sum(1 for y in free if val(y, Q[y]) >= val(y, U[y] - Q[y]))
            lam = sum(lev(y, Q[y] & U[y], sets[y]) for y in free)
            lamU = sum(lev(y, Q[y] & U[y], sorted(U[y])) for y in free)
            PQ = tuple(frozenset([k[i]]) if k[i] is not None else Q[i] & U[i] for i in range(n))
            assert PQ in D and key(PQ) == k, ('P_Q is not a min-frozen state of its key', k)
            scored.append((r, lam, lamU, PQ))
        top = max((r, l) for r, l, _, _ in scored)
        topU = max((r, l) for r, _, l, _ in scored)
        mx = [PQ for r, l, _, PQ in scored if (r, l) == top]
        mxU = [PQ for r, _, l, PQ in scored if (r, l) == topU]
        bm = {}
        for PQ in set(mx) | set(mxU): bm[PQ] = best(PQ)
        rec['nconf'] = len(confs)
        rec['PQs'] = sorted(set(tuple(tuple(sorted(B)) for B in PQ) for PQ in mx))
        rec['PQs'] = [[list(B) for B in PQ] for PQ in rec['PQs']]
        rec['margin'] = min(bm[PQ][0] for PQ in mx)
        rec['margin_U'] = min(bm[PQ][0] for PQ in mxU)
        rec['nrep'] = sum(bm[PQ][1] for PQ in set(mx))
        rec['best_per_max'] = sorted(bm[PQ][0] for PQ in set(mx))
        e = False
        for P in Ps:
            for P2 in byNA[INFO[P][1]]:
                k2 = key(P2)
                if k2 != k and dstar[k2] < dstar[k] and t4(P, P2): e = True; break
            if e: break
        rec['t4edge'] = e
    return {'f': ns['f'], 'n': n, 'm': m, 'keys': out}


if __name__ == '__main__':
    d = json.loads(sys.argv[1])
    r = zmove(d['sets'], d['vals'], d.get('m'))
    print('f =', r['f'])
    for k, rec in sorted(r['keys'].items(), key=lambda t: str(t[0])):
        if rec['dstar'] > 0: print(list(k), rec)
