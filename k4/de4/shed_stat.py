"""Is broad shed-completability (K4.DE4V3R.SHED2) a property of maxima, or of every state? EVIDENCE only.

For random instances (40 of the family advt4r of adv_t4.py and 40 random R1-cores, seed 77): every non-completable
(V3)-valid state with leftover goods, by its distance to the largest level sum, and how many are broad-shed-completable.
    python3 k4/de4/shed_stat.py"""
import sys, os, random, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import refine as RF, shed as SH, adv_t4
SH.MODE = 'broad'
CD = RF.CD; CT = CD.CT; T = CD.T; S = CD.S
from de4lib import leftover
print('$ python3 k4/de4/shed_stat.py')
C = collections.Counter()
for src, mk in (('advt4r', lambda r: adv_t4.make(r, resid=True)), ('rand', CD.random_r1)):
    rng = random.Random(77)
    n = 0
    while n < 40:
        I = mk(rng)
        if I is None:
            continue
        n += 1
        All, ph, P = CT.states(I)
        v3 = [(Y, p) for Y, p in zip(All, ph) if T.v3ok(I, Y)]
        P3 = max(p for _, p in v3)
        Cm = S.Comp(I)
        for Y, p in v3:
            if not leftover(I, Y) or Cm.ok([list(A) for A in Y]):
                continue
            d = P3 - p
            key = '%s, %s below the largest level sum' % (src, '0' if d == 0 else '1-2' if d <= 2 else '3-5' if d <= 5 else '6+')
            C[key + ': non-completable'] += 1
            if SH.shed_ok(I, Y, Cm) is not None:
                C[key + ': broad-shed-completable'] += 1
for k in sorted(C):
    print('%6d  %s' % (C[k], k))
