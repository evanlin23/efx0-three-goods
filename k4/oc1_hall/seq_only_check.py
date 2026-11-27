"""A sequential-only two-move start (proof/k4-matching's smallest 4b-type n = 4 start; k4/oc1_hall.md §23.4 item 4),
re-verified here: no one-move repair, and no repairing pair of moves (from dangerous agents; the second from agents
dangerous after the first) is vertex-disjoint.

    python3 k4/oc1_hall/seq_only_check.py
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, bundles_of, frozen_set
from sdclib import Enc
from oc_absorb import extends_A
import de_free as DF
DF.CHAIN_ONLY = False
sets = [[0, 4, 5, 6], [1, 2, 3, 5], [1, 3, 5, 6], [2, 4, 6]]; vals = [[2, 3, 10, 6], [2, 8, 3, 4], [3, 5, 7, 6], [4, 2, 3]]
I = Inst(sets, vals, 7); E = Enc(sets, vals, 7); Y = picks(I, (3, 1, 2, 0)); P = Picks(I, Y); base = base_of_picks(I, Y)
print('picks', Y, 'J', P.J, 'F', P.F, 'D', P.D)
mv1 = DF.moves(E, base, describe=True, all_desc=True)
print('one-move repairs:', sum(1 for b2 in mv1 if extends_A(E, b2, 1)))
tot = disj = 0; ex = None
for b2, ds in mv1.items():
    B2 = bundles_of(I, b2); F2 = set(frozen_set(I, b2)); J2 = [g for g in range(7) if b2[g] < 0]
    D2 = [i for i in F2 if any(g in I.R[i] for g in J2)]
    for b3, ds3 in DF.moves(E, b2, describe=True, all_desc=True).items():
        if not extends_A(E, b3, 1): continue
        for k1, p1, h1 in ds:
            if p1[0] not in P.D: continue
            for k3, p3, h3 in ds3:
                if p3[0] not in D2: continue
                tot += 1; disj += not (set(p1) & set(p3))
                if ex is None: ex = ((k1, p1, dict(h1)), (k3, p3, dict(h3)))
print('repairing pairs (first from D at the picks, second from D after it):', tot, '; vertex-disjoint:', disj)
print('example:', ex)
