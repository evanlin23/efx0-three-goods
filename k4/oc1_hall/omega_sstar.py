"""Proposition 5 (k4/oc1_hall.md §9): at serial-dictatorship picks, if some unfrozen agent o has
omega_o = |J| - |N_1(o)| <= 1 (N_1(o) = the unfrozen agents other than o), the picks have an S* completion with owner o
(all junk but at most one good into the slots; X_o has at most two goods, both unwanted).  Checks the claim with the
raw S* enumeration on every distinct start, and records the least omega over unfrozen owners at the hard starts.

    python3 k4/oc1_hall/omega_sstar.py SRC
"""
import sys, os, itertools, collections, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, shaped_completion
from chain_shapes import s_star_owners
from min_frozen import load

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/oc1_hall/omega_sstar.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > 5: continue
        I = Inst(sets, vals, m, name); seen = set()
        for od in itertools.permutations(range(n)):
            Y = picks(I, od)
            if Y in seen: continue
            seen.add(Y); P = Picks(I, Y); base = base_of_picks(I, Y)
            U = [o for o in range(n) if o not in P.F]
            holders = U
            om = {o: len(P.J) - (len(U) - 1) for o in U}
            C['distinct starts'] += 1
            for o in U:
                if om[o] <= 1:
                    C['owner tests with omega <= 1'] += 1
                    if not shaped_completion(I, base, o, holders):
                        C['PROPOSITION 5 FAILS'] += 1; print('FAIL', name, json.dumps((sets, vals)), Y, o, flush=True)
            if not s_star_owners(I, base):
                C['hard starts'] += 1; C['  hard: least omega over unfrozen owners %d' % min(om.values())] += 1
                C['  hard: |F| = %d, least omega %d' % (len(P.F), min(om.values()))] += 1
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
