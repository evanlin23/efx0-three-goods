"""ROUND+ at n = 3 is false: ksens's N3K5+ (k4/ksens/refute_oc1_k5_n3.py, k4/ksens.md §8), re-checked with this
workstream's code.  N3K5 x100 with its zeros replaced by 1, 2, 3, ... (every good valued, k = m = 6): from the start
(4, 5, 1), order (1, 0, 2), no round of vertex-disjoint chains has a completion; two rounds repair it.
Checks: rnd.c (Lemma RC, every EFX allocation; Lemma RC2 for two rounds) and bruter.py (forward simulation of every
round and every completion).
    python3 kgen/rounds/n3k5plus.py"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import rndlib, bruter
V = [[300, 1, 2200, 2300, 3800, 4300], [2, 1500, 1700, 2700, 4000, 4300], [3, 100, 4, 5, 200, 400]]
res, ne = rndlib.analyze(V)
print('N3K5+ =', V, '| complete EFX allocations:', ne)
for r in res:
    print('  start', r['picks'], 'order', r['order'], {k: r['counts'][k] for k in ('EXT1', 'OC1', 'RND1', 'RNDP1', 'MD')})
r = next(r for r in res if r['picks'] == (4, 5, 1))
two, md = rndlib.two_rounds(V, list(r['picks']))
b = bruter.classify(V, (1, 0, 2), two=True)
print('start (4, 5, 1): rnd.c one round', r['counts']['RND1'], '| two rounds (Lemma RC2) reachable EFX allocations', two,
      '| bruter.py', {k: b[k] for k in ('ext_1', 'oc1', 'rnd_free', 'rnd_1', 'rnd2_1', 'n_round_states')})
ok = r['counts']['RND1'] == 0 and two > 0 and not b['rnd_1'] and not b['rnd_free'] and b['rnd2_1']
print('OK: one round fails at n = 3 with every good valued; two rounds repair' if ok else 'NOT CONFIRMED')
