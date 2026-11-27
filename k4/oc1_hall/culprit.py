"""Theorem A4 shape (k4/oc1_hall.md §6): at hard starts (no S* completion), for every unfrozen owner r, the frozen
agents k whose demand alone causes the deficit ("culprits": the deficit of r with k treated as satisfied, i.e. k
removed from the agents that must be safe, is <= 0).  Then: does a need chain k -> ... -> r exist (each agent wanting
its predecessor's pick), and does the chain along it, with k taking a minimal improving set of J + {Y_r} and k or r
owning, give an S* completion?  Also whether some culprit chain (any H_0) repairs.

    python3 k4/oc1_hall/culprit.py SRC
"""
import sys, os, itertools, collections, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, bundles_of, frozen_set, deficit
from chain_shapes import s_star_owners
from greedy_rules import canonical_paths, apply_chain
from min_frozen import load


def deficits_without(I, base, r, skip):
    B = bundles_of(I, base); F = set(frozen_set(I, base))
    holders = [j for j in range(I.n) if len(B[j]) <= 1 and j not in F]
    fl = [j for j in range(I.n) if j not in holders and j not in skip]
    return deficit(I, base, r, holders, fl)[0]


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/oc1_hall/culprit.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > 5: continue
        I = Inst(sets, vals, m, name); seen = set()
        for od in itertools.permutations(range(n)):
            Y = picks(I, od)
            if Y in seen: continue
            seen.add(Y); base = base_of_picks(I, Y)
            if s_star_owners(I, base): continue
            P = Picks(I, Y); C['hard starts'] += 1
            U = [o for o in range(n) if o not in P.F]
            pairs = []
            for r in U:
                for k in P.F:
                    d = deficits_without(I, base, r, {k})
                    if d is not None and d <= 0: pairs.append((r, k))
            C['  some (owner r, single culprit k)'] += bool(pairs)
            C['  some culprit k in D'] += any(k in P.D for r, k in pairs)
            withchain = [(r, k, p) for r, k in pairs for p in canonical_paths(I, P, k) if p[-1] == r]
            C['  some culprit with a need chain k -> r'] += bool(withchain)
            rep = set()
            for r, k, p in withchain:
                pool = [g for g in P.J if g in I.R[k]] + ([Y[r]] if Y[r] is not None and Y[r] in I.R[k] else [])
                imp = [H for q in range(1, len(pool) + 1) for H in itertools.combinations(pool, q) if I.val(k, H) > P.pv[k]]
                for H0 in imp:
                    ow = s_star_owners(I, apply_chain(I, P, base, p, H0))
                    if k in ow: rep.add('k owns')
                    if r in ow: rep.add('r owns')
                    if ow: rep.add('some owner')
            for z in rep: C['  culprit chain to r repairs, ' + z] += 1
            if not withchain and C['shown'] < 5:
                C['shown'] += 1; print('NO CULPRIT CHAIN', name, json.dumps((sets, vals)), 'picks', Y, 'F', P.F, 'D', P.D, 'pairs', pairs, flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
