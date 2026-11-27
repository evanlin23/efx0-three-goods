"""Leximin maxima on every stranding instance of kgen/charity.md (§5, §6): GM4-E, GM4-G, the k = 3 cut of GM4-G,
S'(2..4, 3) and S'(2..3, 4) with default values, and the two CH-F instances.  For each: the leximin-maximal sorted
value vector over partial EFX0 allocations (chlib.leximin_max) and the fewest unallocated goods at it.

    python3 kgen/charity/lex_check.py"""
from chlib import Inst, leximin_max, welfare_max
from stuck_family import build
import w_counterexample as WC

if __name__ == '__main__':
    print('$ python3 kgen/charity/lex_check.py', flush=True)
    cases = [('GM4-E', Inst(4, 7, [{0: 3, 2: 10, 4: 6, 6: 2}, {1: 3, 3: 4, 5: 8, 6: 2}, {2: 4, 3: 2, 6: 3},
                                   {4: 2, 5: 4, 6: 3}])),
             ('GM4-G', Inst(4, 7, [{0: 3, 2: 6, 5: 2, 6: 10}, {1: 1, 4: 6, 5: 8, 6: 4}, {2: 3, 3: 6, 5: 8, 6: 4},
                                   {3: 6, 4: 3, 5: 4, 6: 8}])),
             ('GM4-G cut (k = 3)', Inst(4, 7, [{0: 3, 2: 6, 6: 10}, {1: 1, 4: 6, 5: 8}, {2: 3, 3: 6, 5: 8},
                                               {3: 6, 4: 3, 6: 8}])),
             ('CH-F k4', Inst(9, 14, WC.V4)), ('CH-F k3', Inst(12, 17, WC.V3))]
    for s in (2, 3, 4):
        cases.append(("S'(%d, 3)" % s, build(s, 3, own=True)[0]))
    for s in (2, 3):
        cases.append(("S'(%d, 4)" % s, build(s, 4, own=True)[0]))
    for name, I in cases:
        vec, p, X = leximin_max(I)
        print('%s: n %d m %d | leximin maximum %s with %d unallocated' % (name, I.n, I.m, vec, p), flush=True)
