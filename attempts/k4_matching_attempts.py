"""Reproduces attempts/k4-matching-deficiency.md: the free-slot deficiency is not the number of chains.

For each instance and start below, with the pruning-free brute force mlib.bf_complete (every placement of the junk,
raw EFX0), print the least number d of dummy slots for which some owner has a one-absorber completion (per owner),
and whether some official move (k4/sdc/oc1_mc2_rand.Inst.moves) leads to a state that completes with d = 0, or the
least d one move reaches.

    python3 attempts/k4_matching_attempts.py"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'k4', 'matching'))
import _mpaths  # noqa: F401,E402
from mlib import M  # noqa: E402

CASES = [
    ('gap-ivsetting-n3-m6-n3c23 (K4.MC2 class, k = 4)',
     [[0, 3, 4, 5], [1, 3, 4, 5], [2, 3, 4, 5]], [[1, 6, 4, 8], [2, 5, 4, 8], [3, 6, 5, 7]], (4, 3, 5)),
    ('r36 (k = 4)', [[0, 2, 4, 5], [1, 3, 4, 5], [3, 4, 5]], [[2, 4, 8, 7], [8, 10, 3, 4], [4, 3, 2]], (4, 3, 5)),
    ('PW5 (k = 5)', [[0, 5, 6, 7, 8], [1, 5, 6, 7, 8], [2, 5, 6, 7, 8], [0, 1, 2, 3], [0, 1, 2, 4]],
     [[10, 9, 8, 7, 6]] * 3 + [[6, 4, 2, 1], [6, 4, 2, 1]], (0, 1, 2, 3, 4)),
    ('RD5 (k = 5)', [[0, 3, 4, 5, 1], [1, 2, 3], [1, 3, 4, 2], [0, 2, 6, 5]],
     [[26, 44, 24, 33, 57], [12, 11, 6], [9, 6, 1, 8], [36, 53, 4, 47]], (1, 3, 4, 2)),
]


def bf_def(I, base, owners=None, dmax=4):
    for d in range(dmax + 1):
        if any(I.bf_complete(base, d, 'oa', o) for o in (owners if owners is not None else range(I.n))): return d
    return '>%d' % dmax


if __name__ == '__main__':
    for name, sets, vals, Y in CASES:
        I = M(sets, vals, None, name); base = [[g] for g in Y]
        print(name, 'picks', list(Y), 'junk', I.junk(base), 'frozen', I.frozen(base), 'nu', I.nu())
        print('   deficiency per owner (brute force):', {o: bf_def(I, base, [o]) for o in range(I.n)})
        after = [bf_def(I, b, dmax=2) for b in I.moves(base)]
        print('   states after one move: %d; least deficiency after one move: %s; repairing moves: %d'
              % (len(after), min(after, key=lambda x: (isinstance(x, str), x)), sum(1 for x in after if x == 0)))
