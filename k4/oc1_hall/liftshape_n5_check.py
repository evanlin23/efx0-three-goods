"""5_pure idx 164 (compute/k4-oc1max-cert's first n = 5 two-move start; proof/k4-matching's refutation of LIFT-SHAPE+
item 3, attempts/k4-matching-lift-shape.md on that branch), re-verified with this note's tools (k4/oc1_hall.md §23.4
item 4): hard perfect start, no one-move repair, one holder z; among the repairing pairs of sequential moves, none has
a second chain ending at z that gives z its favourite good.

    python3 k4/oc1_hall/liftshape_n5_check.py
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, Picks, base_of_picks, bundles_of
from max_matching import nu
from sdclib import Enc
from oc_absorb import extends_A
import de_free as DF
DF.CHAIN_ONLY = False
sets = [[0, 2, 3, 7], [1, 2, 6, 7], [3, 4, 5, 6], [3, 4, 5, 7], [4, 5, 6, 7]]; vals = [[1, 8, 6, 4], [4, 8, 2, 7], [6, 7, 3, 5], [7, 10, 2, 6], [7, 5, 3, 6]]
I = Inst(sets, vals, 8); E = Enc(sets, vals, 8); Y = (7, 2, 3, 5, 4); P = Picks(I, Y); base = base_of_picks(I, Y)
U = [i for i in range(I.n) if i not in P.F and Y[i] is not None]
print('picks', Y, 'nu', nu(I), 'J', P.J, 'F', P.F, 'D', P.D, 'receivers', U)
print('one-absorber at the picks:', extends_A(E, base, 1))
mv1 = DF.moves(E, base, describe=True, all_desc=True)
print('one-move repairs:', sum(1 for b2 in mv1 if extends_A(E, b2, 1)), 'of', len(mv1))
z = U[0]; fav = max(I.R[z], key=lambda g: I.key[z][g])
print('holder z =', z, ', its favourite good', fav)
pairs = shape3 = strict = 0; ex = None
for b2, ds in mv1.items():
    for b3, ds3 in DF.moves(E, b2, describe=True, all_desc=True).items():
        if not extends_A(E, b3, 1): continue
        pairs += 1
        B3 = bundles_of(I, b3)
        ok3 = any(k3 == 'chain' and p3[-1] == z for k3, p3, h3 in ds3) and fav in B3[z]
        shape3 += ok3
        if ok3:
            print('  loose match: first', [d[:3] for d in ds][:2], '; second', [d[:3] for d in ds3][:2], '; z ends with', B3[z])
        # LIFT-SHAPE+ exactly: P1 a junk-free chain from D to z whose H0 (2 goods, inside J + {y_z}) is improving for
        # another dangerous agent; P2 a canonical chain (no junk after x0) ending at z, with z holding fav at the end
        for k1, p1, h1 in ds:
            if not (k1 == 'chain' and p1[0] in P.D and p1[-1] == z and all(not h1.get(i) for i in range(1, len(p1)))): continue
            H0 = tuple(h1.get(0, ()))
            if len(H0) != 2 or not any(q != p1[0] and q in P.D and I.val(q, H0) > P.pv[q] for q in range(I.n)): continue
            for k2, p2, h2 in ds3:
                if k2 == 'chain' and p2[-1] == z and all(not h2.get(i) for i in range(1, len(p2))) and fav in B3[z]:
                    strict += 1; print('  LIFT-SHAPE+ pair:', p1, H0, ';', p2, dict(h2))
        if ex is None: ex = (ds[0][:2], ds3[0][:2])
print('repairing (first move, second move) state pairs:', pairs, '; with a second chain ending at z and z holding its favourite:', shape3)
print('example repairing pair:', ex)
print('repairing pairs of the exact LIFT-SHAPE+ form (items 2 and 3):', strict)
