"""One round of vertex-disjoint chains (ocsat multi) on every start of the known OC1 counterexamples (k4/ksens.md §6).

    python3 k4/ksens/round_known.py"""
import json
import _paths
import ocsat, fam_ladder, fam_pwr1
from refute_oc1_r1 import pw_flat, pw_nf

rows = [[34, 0, 0, 0, 38, 35, 37, 33], [0, 10, 5, 0, 0, 4, 2, 0], [0, 2, 0, 0, 3, 0, 1, 0], [52, 54, 53, 4, 0, 0, 0, 51]]
KGEN = ([[g for g, x in enumerate(r) if x > 0] for r in rows], [[x for x in r if x > 0] for r in rows], 8)
CASES = {'kgen-n4': KGEN, 'PW5': fam_ladder.clean(3, 2, 4), 'PW436': fam_ladder.clean(4, 3, 6),
         'PWR1-6': fam_pwr1.make(3, 3, 5, [0]), 'NF2-6': pw_flat(3, 3, 5, (0,)), 'NF1R1-6': pw_nf(4, 3, 5, (0,))}

if __name__ == '__main__':
    print('$ python3 k4/ksens/round_known.py: one round of vertex-disjoint chains on every start', flush=True)
    for name, (sets, vals, m) in CASES.items():
        O = ocsat.OC(sets, vals, m); n = len(sets)
        C = {'starts': 0, 'need a chain (A=1)': 0, 'one chain fails (A=1)': 0, 'one round fails (A=1)': 0, 'one round fails (free)': 0}
        for Y in ocsat.starts(sets, vals, m):
            b = ocsat.bases_of(Y, n); C['starts'] += 1
            if O.holds(b, chain='none', A=1): continue
            C['need a chain (A=1)'] += 1
            C['one chain fails (A=1)'] += not O.holds(b, chain='need', A=1)
            C['one round fails (A=1)'] += not O.holds(b, chain='need', A=1, multi=True)
            C['one round fails (free)'] += not O.holds(b, chain='any', multi=True)
        print(name, 'k', max(map(len, sets)), 'n', n, 'm', m, C, flush=True)
        O.close()
