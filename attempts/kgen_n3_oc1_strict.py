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
