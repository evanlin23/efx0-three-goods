"""Verify the counterexample D1H-X (k4/d1.md §5) to sub-lemma D1-H, Conjecture D1-LONG and the canonical-chain form of
Finding D1 (k4/oc1_hall.md §21), with two independent implementations:
  (1) k4/d1/d1lib.py (this workstream: raw EFX0 by enumeration);
  (2) k4/oc1_hall/ohlib.py + k4/sdc/oc_absorb.extends_A (the Hall session's raw enumeration and the SAT test).
Checks: the picks of the order have no one-absorber completion; D = {k}; every canonical chain from k has HEAD; for
every canonical chain and EVERY improving H0 (not only minimal), the state after the chain has no S* completion owned
by k or by the head; and the ED chain in which the head also takes one junk good does repair (owner k).

    python3 k4/d1/verify_cex.py
"""
import sys, os, itertools, json
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import d1lib as L

CEX = {
    'D1H-X (found)': ([[0, 1, 5, 7], [3, 4, 6, 7], [0, 2, 5, 7]], [[26, 3, 25, 27], [19, 17, 25, 30], [9, 14, 7, 29]], 8, (0, 1, 2)),
    'D1H-Y (strict core)': ([[0, 4, 3, 5], [2, 6, 4, 5], [0, 1, 3, 5]], [[20, 13, 21, 23], [17, 14, 18, 23], [8, 11, 7, 23]], 7, (0, 1, 2)),
    'D1H-X (shrunk)': ([[0, 1, 5, 7], [3, 4, 6, 7], [0, 2, 5, 7]], [[26, 3, 25, 27], [2, 17, 18, 19], [4, 5, 2, 10]], 8, (0, 1, 2)),
}


def mine(sets, vals, m, od):
    I = L.Inst(sets, vals, m); Y = L.sd_picks(I, od); S = L.Start(I, Y)
    out = dict(picks=Y, J=S.J, F=S.F, D=S.D, one_absorber_at_picks=L.one_absorber(I, S.B))
    k = S.D[0]; rows = []
    for path in L.canonical_chains(S, k):
        Pi = L.pool(S, path); Pk = [g for g in Pi if g in I.R[k]]
        imp = [frozenset(H) for r in range(1, len(Pk) + 1) for H in itertools.combinations(Pk, r) if I.val(k, H) > S.p[k]]
        for H0 in imp:
            B2 = L.apply_chain(S, path, H0); head, crowded, F2 = L.obstacles(S, path, H0, B2)
            rows.append((path, sorted(H0), head, L.sstar(I, B2, k), L.sstar(I, B2, path[-1])))
    out['chains'] = rows
    # ED chains with one junk good at the head
    eds = []
    for path in L.canonical_chains(S, k):
        z = path[-1]; a = Y[path[-2]]
        for h in S.J:
            if I.val(z, [a, h]) <= S.p[z]: continue
            Pi = [g for g in L.pool(S, path) if g != h]; Pk = [g for g in Pi if g in I.R[k]]
            imp = [frozenset(H) for r in range(1, len(Pk) + 1) for H in itertools.combinations(Pk, r) if I.val(k, H) > S.p[k]]
            mins = [H for H in imp if not any(K < H for K in imp)]
            for H0 in mins:
                B = [list(b) for b in S.B]; B[z] = [a, h]; B[k] = sorted(H0)
                for i in range(1, len(path) - 1): B[path[i]] = [Y[path[i - 1]]]
                X = L.sstar(I, B, k, witness=True)
                if X: eds.append((path, h, sorted(H0), X))
    out['ED repairs with head junk'] = eds
    return out


def hall(sets, vals, m, od):
    sys.path.insert(0, os.path.join(ROOT, 'k4', 'oc1_hall')); sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
    from ohlib import Inst, picks, Picks, base_of_picks, bundles_of, frozen_set, shaped_completion, absorb_brute
    from greedy_rules import canonical_paths, apply_chain
    from sdclib import Enc
    from oc_absorb import extends_A
    I = Inst(sets, vals, m); E = Enc(sets, vals, m); Y = picks(I, od); base = base_of_picks(I, Y); P = Picks(I, Y)
    out = dict(picks=Y, sat_one_absorber=extends_A(E, base, 1), brute_one_absorber=sorted(absorb_brute(I, base)), D=P.D)
    k = P.D[0]; anyok = False
    for path in canonical_paths(I, P, k):
        xt = path[-1]
        if xt in P.F: continue
        pool = [g for g in P.J if g in I.R[k]] + ([Y[xt]] if Y[xt] in I.R[k] else [])
        for r in range(1, len(pool) + 1):
            for H0 in itertools.combinations(pool, r):
                if I.val(k, H0) <= P.pv[k]: continue
                b2 = apply_chain(I, P, base, path, H0); B2 = bundles_of(I, b2); F2 = set(frozen_set(I, b2))
                holders = [j for j in range(I.n) if len(B2[j]) <= 1 and j not in F2]
                anyok |= shaped_completion(I, b2, k, holders) or shaped_completion(I, b2, xt, holders)
    out['some canonical chain, any H0, S* owned by k or head'] = anyok
    return out


if __name__ == '__main__':
    print('$ python3 k4/d1/verify_cex.py')
    for name, (sets, vals, m, od) in CEX.items():
        print('==', name, json.dumps((sets, vals)), 'm', m, 'order', od)
        a = mine(sets, vals, m, od); b = hall(sets, vals, m, od)
        for kk, v in a.items():
            if kk == 'chains':
                for row in v: print('  mine: chain %s H0 %s HEAD %s  S* owner k %s  S* owner head %s' % row)
            else: print('  mine:', kk, v)
        for kk, v in b.items(): print('  hall:', kk, v)
        hard = not a['one_absorber_at_picks'] and not b['sat_one_absorber'] and not b['brute_one_absorber'] and len(a['D']) == 1
        allhead = all(r[2] for r in a['chains'])
        ownk = not any(r[3] for r in a['chains'])
        either = ownk and not any(r[4] for r in a['chains']) and not b['some canonical chain, any H0, S* owned by k or head']
        print('  VERDICT hard start, D = {k}, every canonical chain has HEAD:', hard and allhead)
        print('  VERDICT no canonical chain, any H0, owner k (refutes D1-H, D1-LONG, canonical Finding D1):', hard and allhead and ownk)
        print('  VERDICT ... nor owner k or head (refutes the canonical form of OC1-ED* (b)):', hard and allhead and either)
        print('  VERDICT an ED chain whose head adds one junk good repairs, owner k:', bool(a['ED repairs with head junk']))
