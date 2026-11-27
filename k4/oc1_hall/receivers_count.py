"""The coordinator's counting sketch for OC1^max with nu = n (k4/oc1_hall.md §20).  At every one-absorber-hard start
whose picks form a maximum matching: t2 = frozen agents whose junk goods contain a danger triangle (three junk goods,
every pair worth more than the pick), t1 = the other dangerous frozen agents with a junk danger set, r = receivers
(unfrozen agents holding a pick).  Distribution of (t2, t1, r), and how often r < 2 * t2 (the sketch's failure regime).

    python3 k4/oc1_hall/receivers_count.py SRC
"""
import sys, os, itertools, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks
from max_matching import nu
from sdclib import Enc
from oc_absorb import extends_A
from min_frozen import load

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter()
    print('$ python3 k4/oc1_hall/receivers_count.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > 5: continue
        I = Inst(sets, vals, m, name); E = Enc(sets, vals, m); N = nu(I); seen = set()
        for od in itertools.permutations(range(n)):
            Y = picks(I, od)
            if Y in seen: continue
            seen.add(Y)
            if sum(1 for y in Y if y is not None) != N: continue
            b = base_of_picks(I, Y)
            if extends_A(E, b, 1): continue
            P = Picks(I, Y)
            t2 = t1 = 0
            for x in P.D:
                Jx = P.Jv[x]
                tri = any(all(I.val(x, pr) > P.pv[x] for pr in itertools.combinations(T, 2)) for T in itertools.combinations(Jx, 3))
                dang = any(I.val(x, T) > P.pv[x] for r_ in (2, 3) for T in itertools.combinations(Jx, r_))
                if tri: t2 += 1
                elif dang: t1 += 1
            r = sum(1 for i in range(n) if i not in P.F and Y[i] is not None)
            C['hard maximum-matching starts'] += 1
            C['  (t2, t1, r) = (%d, %d, %d)' % (t2, t1, r)] += 1
            C['  r < 2 t2'] += r < 2 * t2
            if r < 2 * t2 and C['shown'] < 2:
                C['shown'] += 1
                import json
                print('R < 2 T2', name, json.dumps((sets, vals)), 'order', od, 'picks', Y, 'F', P.F, 'D', P.D, 't2', t2, 'r', r, flush=True)
            C['  t2 >= 1'] += t2 >= 1
    for k in sorted(C): print(k, C[k])
