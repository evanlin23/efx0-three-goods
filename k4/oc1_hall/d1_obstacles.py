"""Lemma D1-red (k4/oc1_hall.md §21): obstacle census for canonical chains from the unique dangerous agent.
At every one-absorber-hard start whose picks form a maximum matching and that has exactly one dangerous agent k: for
every canonical chain k = x_0 -> ... -> x_t (each x_i wants Y_{x_{i-1}}, takes no junk; x_t unfrozen at the picks) and
every inclusion-minimal improving H_0 inside (J + {Y_{x_t}}) & R_k, with owner k, record which obstacles of Lemma
D1-red occur after the chain:
  (a) HEAD: x_t is frozen afterwards and threatened by W'_k = H_0 + J' at its new value;
  (b) CROWD: some unfrozen single-good holder u has |H_0 & R_u| >= 2 and v_u(H_0 & R_u) > v_u(B'_u);
  (c) KWANT: k wants (after the chain) a good held by another agent;
  (d) OTHER: none of (a)-(c), yet no S* completion with owner k (would contradict the lemma);
and whether an S* completion owned by k exists.  Prints the smallest start (by n, m) for each obstacle among the
chains that fail.

    python3 k4/oc1_hall/d1_obstacles.py SRC
"""
import sys, os, itertools, collections, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, bundles_of, frozen_set, threatened, wants_good, shaped_completion
from max_matching import nu
from greedy_rules import canonical_paths, apply_chain
from sdclib import Enc
from oc_absorb import extends_A
from min_frozen import load

SMALL = {}

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter()
    print('$ python3 k4/oc1_hall/d1_obstacles.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > 5: continue
        I = Inst(sets, vals, m, name); E = Enc(sets, vals, m); N = nu(I); seen = set()
        for od in itertools.permutations(range(n)):
            Y = picks(I, od)
            if Y in seen: continue
            seen.add(Y); P = Picks(I, Y)
            if len(P.D) != 1 or sum(1 for y in Y if y is not None) != N: continue
            base = base_of_picks(I, Y)
            if extends_A(E, base, 1): continue
            k = P.D[0]; C['starts'] += 1; anyok = False; anyfree = False
            for path in canonical_paths(I, P, k):
                xt = path[-1]
                if xt in P.F: continue
                pool = [g for g in P.J if g in I.R[k]] + ([Y[xt]] if Y[xt] is not None and Y[xt] in I.R[k] else [])
                imp = [H for r in range(1, len(pool) + 1) for H in itertools.combinations(pool, r) if I.val(k, H) > P.pv[k]]
                for H0 in [H for H in imp if not any(set(K) < set(H) for K in imp)]:
                    b2 = apply_chain(I, P, base, path, H0); B2 = bundles_of(I, b2)
                    F2 = set(frozen_set(I, b2)); J2 = [g for g in range(m) if b2[g] < 0]
                    holders = [j for j in range(n) if len(B2[j]) <= 1 and j not in F2]
                    ok = shaped_completion(I, b2, k, holders)
                    pv2 = [I.val(i, B2[i]) for i in range(n)]
                    Wk = list(H0) + J2
                    obs = set()
                    if xt in F2 and threatened(I, xt, pv2[xt], Wk): obs.add('a HEAD')
                    for u in holders:
                        if u == k: continue
                        Hu = [g for g in H0 if g in I.R[u]]
                        if len(Hu) >= 2 and I.val(u, Hu) > pv2[u]: obs.add('b CROWD')
                    if any(wants_good(I, B2, k, g) for g in range(m) if b2[g] >= 0 and b2[g] != k): obs.add('c KWANT')
                    if not obs and not ok: obs.add('d OTHER')
                    C['chains'] += 1; C['chains repairing'] += ok
                    for o in obs:
                        C['  chains with obstacle %s' % o] += 1
                        C['  chains with obstacle %s that still repair' % o] += ok
                        if not ok:
                            key = (n, m)
                            if o not in SMALL or key < SMALL[o][0]:
                                SMALL[o] = (key, name, sets, vals, list(od), list(Y), k, list(path), list(H0))
                    if not obs: C['  chains with no obstacle'] += 1; C['  chains with no obstacle that repair'] += ok
                    if not (obs & {'a HEAD', 'b CROWD'}): anyfree = True
                    anyok |= ok
            C['starts with a repairing canonical chain (owner k, minimal H0)'] += anyok
            C['starts with a canonical chain free of HEAD and CROWD'] += anyfree
            if not anyfree:
                C['  starts where every canonical chain has HEAD or CROWD'] += 1
                if C['shown nofree'] < 3:
                    C['shown nofree'] += 1
                    print('NO FREE CHAIN', name, json.dumps((sets, vals)), 'order', od, 'picks', Y, 'k', k, flush=True)
    for k_ in sorted(C): print(k_, C[k_])
    for o, (key, name, sets, vals, od, Y, k, path, H0) in sorted(SMALL.items()):
        print('SMALLEST failing chain with obstacle', o, name, key, json.dumps((sets, vals)), 'order', od, 'picks', Y, 'k', k, 'chain', path, 'H0', H0)
