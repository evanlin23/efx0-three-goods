"""Smallest test instances for Conjecture R2 (TTC session; k4/oc1_hall.md §23.4): one-absorber-hard starts whose picks
form a maximum matching and that have at least two receivers (unfrozen pick holders), in this note's data sets; the
smallest by (n, m, |J|) is printed, with the number of such starts per data set.

    python3 k4/oc1_hall/r2_smallest.py SRC
"""
import sys, os, itertools, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks
from max_matching import nu
from sdclib import Enc
from oc_absorb import extends_A
from min_frozen import load

if __name__ == '__main__':
    src = sys.argv[1]; best = None; cnt = 0
    print('$ python3 k4/oc1_hall/r2_smallest.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > 5: continue
        I = Inst(sets, vals, m, name); E = Enc(sets, vals, m); N = nu(I); seen = set()
        for od in itertools.permutations(range(n)):
            Y = picks(I, od)
            if Y in seen: continue
            seen.add(Y)
            if sum(1 for y in Y if y is not None) != N: continue
            P = Picks(I, Y); U = [i for i in range(n) if i not in P.F and Y[i] is not None]
            if len(U) < 2: continue
            if extends_A(E, base_of_picks(I, Y), 1): continue
            cnt += 1; key = (n, m, len(P.J))
            if best is None or key < best[0]: best = (key, name, sets, vals, od, Y, P.D, U)
    print('hard maximum-matching starts with >= 2 receivers:', cnt)
    if best: print('smallest', best[0], best[1], json.dumps((best[2], best[3])), 'order', best[4], 'picks', best[5], 'D', best[6], 'receivers', best[7])
