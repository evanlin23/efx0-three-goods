"""Proposition D1-C' and its residual cases (k4/oc1_hall.md §21).  At every one-absorber-hard start with D = {k}, for
every canonical chain P from k without HEAD (Pi = J + B_{x_t}, Pi_k = Pi & R_k):
  U' = agents off P, unfrozen at the picks, valuing >= 2 goods of Pi_k; b_u = u's favourite good of Pi.
  DUAL (Lemma D1-C0, proved): every set B of pairwise distinct favourites inside J has v_k(Pi_k - B) > p_k.
  PROP (Proposition D1-C', proved): if the favourites of U' are pairwise distinct and lie in J, every minimal improving
       H_0 inside Pi_k - B(U') either crowds the head or leaves an S* completion owned by k.
       A crowded head is compensated by its released pick Y_{x_t} when Y_{x_t} is not in H_0 (also proved).
  Residual cases: C-a two members of U' share a favourite; C-c a favourite is Y_{x_t}; C-b every minimal improving
       H_0 inside Pi_k - B(U') crowds the head and contains Y_{x_t}.  For each, whether some minimal improving H_0 on P repairs.

    python3 k4/oc1_hall/d1_crowd.py SRC
"""
import sys, os, itertools, collections, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks
from greedy_rules import canonical_paths
from d1_subcases import analyse
from sdclib import Enc
from oc_absorb import extends_A
from min_frozen import load


def minimal_improving(I, k, pk, ground):
    imp = [H for r in range(1, len(ground) + 1) for H in itertools.combinations(ground, r) if I.val(k, H) > pk]
    return [H for H in imp if not any(set(K) < set(H) for K in imp)]


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter()
    print('$ python3 k4/oc1_hall/d1_crowd.py', *sys.argv[1:], flush=True)
    def bad(tag, *a):
        C[tag] += 1
        if C['shown ' + tag] < 3: C['shown ' + tag] += 1; print(tag, *a, flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > 5: continue
        I = Inst(sets, vals, m, name); E = Enc(sets, vals, m); seen = set()
        for od in itertools.permutations(range(n)):
            Y = picks(I, od)
            if Y in seen: continue
            seen.add(Y); P = Picks(I, Y)
            if len(P.D) != 1: continue
            base = base_of_picks(I, Y)
            if extends_A(E, base, 1): continue
            k = P.D[0]; inst = json.dumps((sets, vals)); C['starts'] += 1
            for path in canonical_paths(I, P, k):
                xt = path[-1]
                if xt in P.F: continue
                Pi = list(P.J) + ([Y[xt]] if Y[xt] is not None else [])
                Pik = [g for g in Pi if g in I.R[k]]
                mins = minimal_improving(I, k, P.pv[k], Pik)
                res = {H0: analyse(I, P, base, k, path, H0) for H0 in mins}
                if any('HEAD' in r[0] for r in res.values()): continue
                C['chains without HEAD'] += 1
                Up = [u for u in range(n) if u not in path and u not in P.F and sum(1 for g in Pik if g in I.R[u]) >= 2]
                fav = {u: max((g for g in Pi if g in I.R[u]), key=lambda g: I.key[u][g]) for u in Up}
                # DUAL on every subset of U' with distinct favourites in J
                for r in range(1, len(Up) + 1):
                    for S in itertools.combinations(Up, r):
                        B = [fav[u] for u in S]
                        if len(set(B)) == len(B) and all(b in P.J for b in B):
                            if I.val(k, [g for g in Pik if g not in B]) <= P.pv[k]: bad('DUAL FAILS', name, inst, Y, path, S)
                Bs = [fav[u] for u in Up]
                distinct = len(set(Bs)) == len(Bs)
                inJ = all(b in P.J for b in Bs)
                anyrep = any(r[1] is not None for r in res.values())
                if not distinct: case = 'C-a (shared favourite)'
                elif not inJ: case = 'C-c (a favourite is the head\'s released pick)'
                else:
                    sub = minimal_improving(I, k, P.pv[k], [g for g in Pik if g not in Bs])
                    if not sub: bad('DUAL FAILS (no improving set avoiding B(U\'))', name, inst, Y, path); continue
                    headfree = False
                    for H0 in sub:
                        obs, comp, F2, crowded, B2 = analyse(I, P, base, k, path, H0)
                        if xt in crowded and Y[xt] in H0: continue
                        headfree = True
                        tag = 'PROP' if xt not in crowded else 'PROP (crowded head compensated by its released pick)'
                        if comp is None: bad(tag + ' FAILS', name, inst, 'order', od, 'picks', Y, 'chain', path, 'H0', H0)
                        else: C['  %s: completion found as proved' % tag] += 1
                    case = 'PROP applies' if headfree else 'C-b (every H0 avoiding B(U\') crowds the head and contains Y_{x_t})'
                C['chains: ' + case] += 1; C['chains: %s, repaired by some minimal H0' % case] += anyrep
                if case.startswith('C-') and C['shown case ' + case] < 3:
                    C['shown case ' + case] += 1
                    print('RESIDUAL', case, name, inst, 'order', od, 'picks', Y, 'k', k, 'chain', path, 'U\'', Up, 'favourites', Bs, 'repaired', anyrep, flush=True)
                if not anyrep and case != 'PROP applies':
                    bad('RESIDUAL CHAIN FAILS ' + case, name, inst, 'order', od, 'picks', Y, 'k', k, 'chain', path)
    for k_ in sorted(C):
        if not k_.startswith('shown'): print(k_, C[k_])
