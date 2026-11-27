"""Two n = 5 starts (proof/k4-matching, attempts/k4-matching-rsd-lstar.md on that branch; the certifier's chunk
5_pure_s5o0) where every settle-and-lift form (OC2-REC, REC-S, RSD with (L*) at each step) fails, re-checked with this
note's tools (k4/oc1_hall.md §24.4): no one-move repair, and OC2 itself (two sequential official moves, de_free.moves,
then a one-absorber completion, SAT) still holds, by two vertex-disjoint chains.

    python3 k4/oc1_hall/round_n5_check.py
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, Picks, base_of_picks
from sdclib import Enc
from oc_absorb import extends_A
import de_free as DF
DF.CHAIN_ONLY = False
CASES = [('5_pure m=10 idx 419', [[0,2,6,7],[1,4,8,9],[3,5,8,9],[4,5,7,9],[6,7,8,9]], [[6,3,10,8],[4,8,2,3],[2,8,4,3],[6,7,5,3],[10,7,2,6]], (6,4,5,9,7)),
         ('5_pure m=11 idx 447', [[0,2,5,8],[1,6,7,8],[3,6,9,10],[4,7,9,10],[5,8,9,10]], [[3,4,8,6],[1,6,8,4],[2,10,6,3],[2,8,3,4],[10,8,3,6]], (5,1,6,7,8))]
for name, sets, vals, Y in CASES:
    m = 1 + max(max(s) for s in sets); I = Inst(sets, vals, m); E = Enc(sets, vals, m); P = Picks(I, Y); base = base_of_picks(I, Y)
    print('=====', name, 'picks', Y, 'J', P.J, 'F', P.F, 'D', P.D, 'one-absorber at picks', extends_A(E, base, 1))
    mv1 = DF.moves(E, base, describe=True, all_desc=True)
    print('  one-move repairs:', sum(1 for b in mv1 if extends_A(E, b, 1)), 'of', len(mv1))
    pairs = disj = 0; ex = None
    for b2, ds in mv1.items():
        for b3, ds3 in DF.moves(E, b2, describe=True, all_desc=True).items():
            if not extends_A(E, b3, 1): continue
            pairs += 1
            if any(not (set(p1) & set(p3)) for _, p1, _ in ds for _, p3, _ in ds3):
                disj += 1
                if ex is None: ex = ([(k, p, dict(h)) for k, p, h in ds][:1], [(k, p, dict(h)) for k, p, h in ds3][:1])
    print('  two-move repairs (state pairs):', pairs, '; with vertex-disjoint moves:', disj, '; example:', ex)
