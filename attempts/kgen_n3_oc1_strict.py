"""Reproduce attempts/kgen-n3-oc1-strict.md: OC1 with chains t >= 1 only (the definition in k4/sdc.md §29) fails at
n = 3, m = 7, k = 5, strict values; OC1 with t >= 0 (the moves k4/sdc/oc_absorb.py tests) holds there.
Three checks: kgen/oc3.c (brute force, maximal-H characterization), kgen/verify_oc1.py (pure Python, every chain
enumerated explicitly), and k4/sdc's SAT pipeline (oc_absorb.extends_A + de_free.iter_chains, t >= 1 filter)."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'kgen'))
from verify_oc1 import replay, sat_replay, all_efx
from oc3lib import brute, ORD

V = [[74, 72, 5, 0, 73, 71, 0], [0, 0, 2, 58, 27, 0, 28], [4, 3, 0, 7, 0, 1, 0]]
ORDER = (0, 2, 1)
r = replay(V, ORDER); s = sat_replay(V, ORDER); b = brute(V)[ORD.index(ORDER)]
print('picks', r['picks'], '| EFX0 allocations', r['EFX0 allocations'])
print('replay: picks have a one-absorber completion:', r['picks: one-absorber completion'] is not None)
print('replay: chain states t>=1: %d, any repairs: %s' % (r['chain states t>=1'], r['repair with t>=1'] is not None))
print('replay: a t=0 move repairs:', r['repair with t=0'])
print('sat:', s)
print('oc3.c: NONE %d STRICT %d CODE %d' % (b['NONE'], b['STRICT'], b['CODE']))
ok = (not r['OC1 (t>=1) holds'] and r['OC1 (t>=0) holds'] and s == {'sat: picks': False, 'sat: t>=1': False, 'sat: t=0': True}
      and b['NONE'] == 0 and b['STRICT'] == 0 and b['CODE'] > 0)
print('OC1 with t>=1 REFUTED, OC1 with t>=0 holds, all three checks agree:', ok)

# n = 2: kgen/oc2.py's explicit chain enumeration, and k4/sdc's SAT pipeline (n = 2) with the t >= 1 filter
import itertools
from oc2 import efx0 as efx2, sd as sd2, states, one_abs
V2 = [[0, 28, 8, 27, 55, 26, 21], [1, 66, 3, 64, 2, 63, 65]]
m = len(V2[0])
Xs = [X for X in ([frozenset(g for g in range(m) if a[g] == i) for i in range(2)] for a in itertools.product(range(2), repeat=m)) if efx2(V2, X)]
res = []
for o in [(0, 1), (1, 0)]:
    y = sd2(V2, o); B = [frozenset([y[i]]) for i in range(2)]; J = [g for g in range(m) if g not in y]
    ok = {0: False, 1: False}
    for tt, nb in states(V2, B, J):
        if not ok[tt] and one_abs(Xs, nb): ok[tt] = True
    res.append((one_abs(Xs, B), ok[1], ok[0]))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'k4', 'sdc'))
import _paths  # noqa
import de_free as DF
from sdclib import Enc
from oc_absorb import extends_A
from sdc_orders import sd as sdk
DF.CHAIN_ONLY = True; DF.HMAX = m; DF.BMAX = m
sets = [[g for g in range(m) if V2[i][g] > 0] for i in range(2)]
E = Enc(sets, [[V2[i][g] for g in sets[i]] for i in range(2)], m); sat = []
for o in [(0, 1), (1, 0)]:
    Y = sdk(E, list(o))[0]; base = [-1] * m
    for i, g in enumerate(Y): base[g] = i
    base = tuple(base); r = [extends_A(E, base, 1), False, False]
    for b2 in set(DF.iter_chains(E, base)):
        ch = sum(1 for i in range(2) if {g for g in range(m) if b2[g] == i} != {g for g in range(m) if base[g] == i})
        k = 1 if ch >= 2 else 2
        if not r[k] and extends_A(E, b2, 1): r[k] = True
    sat.append(tuple(r))
print('n = 2: per order (picks extend, a t>=1 chain repairs, a t=0 move repairs): enumeration', res, 'sat', sat)
print('n = 2: t>=1 REFUTED, t>=0 holds, both checks agree:', res == sat == [(False, False, True)] * 2)
