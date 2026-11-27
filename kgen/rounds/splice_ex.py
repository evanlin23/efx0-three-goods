"""The splice exception (Lemma SPLICE's configuration EX-b, kgen/rounds.md §4.10): a valid REC-S witness (accepted by
k4/oc1max_multi/check_recs.py) whose final allocation is EFX0 but is NOT a one-round witness at the start, in any form
(RNDOZ, RNDPZ, WIDE).  The start itself has one-move repairs (OC1 holds), and ROUND-P holds there by other allocations.
    python3 kgen/rounds/splice_ex.py"""
import sys, os, json
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(ROOT, 'k4', 'oc1max_multi'))
import check_recs, rndlib, verify_k4zero as VZ, recs_vs_rndp as RV
sets = [[1, 2, 3, 5], [1, 3, 5, 6], [1, 2, 3, 6], [0, 2, 4, 5]]
vals = [[2289, 1831, 2530, 1934], [836, 2963, 2033, 642], [1387, 1223, 2254, 1149], [1362, 271, 72, 1386]]
w = {'order': [2, 0, 3, 1], 'k': 3, 'P1': [3, 1], 'T': [0, 4], 'P2': [2, 1], 'H0_2': [2, 6], 'h': 5,
     'X': [[1, 5], [3], [2, 6], [0, 4]]}
y = (1, 6, 3, 5)
V = [[0] * 7 for _ in sets]
for i, (s, vv) in enumerate(zip(sets, vals)):
    for g, v in zip(s, vv): V[i][g] = v
print('instance', json.dumps(V), 'order', w['order'], 'picks', y)
print('REC-S witness: E(3) = (3, 1), T = {0, 4}; P2 = (2, 1), H0 = {2, 6}; h = 5 = Y_3 to agent 0; X =', w['X'])
print('check_recs (multi):', check_recs.check({'sets': sets, 'vals': vals, 'picks': list(y), 'witness': w}))
print('X raw EFX0:', VZ.efx0(V, w['X']))
print('round structures at X (RNDOZ / RNDPZ / WIDE):', RV.structures(V, y, w['X'], False), RV.structures(V, y, w['X'], True),
      RV.structures(V, y, w['X'], True, True))
print('why: agent 3 holds no pick, its pick 5 lies with agent 0, which keeps its pick 1; agent 0 would be an end, and',
      'v0(5) =', V[0][5], '<= v0(1) =', V[0][1])
res, _ = rndlib.oc1z(V); r = next(r for r in res if tuple(r['picks']) == y)
print('the start (rnd.c):', {k: r[k] for k in ('EXT1', 'OC1', 'OC1P', 'RND1Z', 'RNDOZ', 'RNDPZ', 'MD')})
