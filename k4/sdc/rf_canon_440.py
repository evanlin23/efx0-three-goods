"""TTC's canonical RF-exists rule YRMH-F (k4/ttc.md §14.9; k4/ttc/rf_diag.feasible_sd) at the k = 4 counterexample to
RF's every-order form (5_pure #440, K4.SDC.RF): for every order o giving the failing start Y = (3,6,7,4,5) and the
receiver u = 4, compare the rotation (u, o - u), plain YRMH and YRMH-F; OC1 by oc1_mc2_rand.Inst.check.
    python3 k4/sdc/rf_canon_440.py"""
import os, sys, itertools
import _paths  # noqa: F401
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'ttc'))
from oc1_mc2_rand import Inst
import rf_diag as D
from rf_rules import yrmh

SETS = [[0, 3, 5, 7], [1, 2, 3, 6], [1, 2, 6, 7], [4, 5, 6, 7], [4, 5, 6, 7]]
VALS = [[5, 19, 13, 10], [9, 6, 17, 12], [3, 5, 7, 6], [14, 1, 7, 4], [18, 4, 11, 5]]

if __name__ == '__main__':
    print('$ python3 k4/sdc/rf_canon_440.py')
    I = Inst(SETS, VALS); Y = (3, 6, 7, 4, 5); u = 4
    ords = [o for o in itertools.permutations(range(I.n)) if I.sd(o) == Y]
    print('Y', Y, I.check(Y), 'receiver', u, 'orders giving Y', ords)
    for o in ords:
        q = [u] + [a for a in o if a != u]
        rot = I.sd(q); Zy = yrmh(I, Y, o, u)[0]; Zf, od = D.feasible_sd(I, Y, q)
        print('o', o, '| ROT', rot, I.check(rot), '| YRMH', Zy, I.check(Zy), '| YRMH-F', Zf, 'order', od,
              I.check(Zf) if Zf != ('stuck',) else 'stuck', '| maximum', sum(z is not None for z in Zf) == I.n)
