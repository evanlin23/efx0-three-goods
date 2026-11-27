"""Frozen slots ARE needed after one move (refutes k4/oc1_hall.md §13's "frozen slots are not needed" at n = 4;
instance from proof/k4-matching, k4/matching/n4_walk.py).  At the hard start below, five one-move states have a
one-absorber completion and none has an S* completion (any owner): the completions give a frozen agent a junk good,
compensated as in Lemma 1's (S1).

    python3 k4/oc1_hall/frozen_slot_cex.py
"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, bundles_of, absorb_brute, frozen_set
from chain_shapes import s_star_owners
from sdclib import Enc
from oc_absorb import extends_A
import de_free as DF
DF.CHAIN_ONLY = False
sets = [[0, 2, 5, 7], [1, 5, 6, 7], [2, 3, 4, 6], [3, 4, 6, 7]]; vals = [[2, 10, 5, 4], [2, 3, 10, 6], [10, 6, 3, 8], [5, 3, 7, 6]]
I = Inst(sets, vals, 8); E = Enc(sets, vals, 8)
ords = [od for od in itertools.permutations(range(4)) if picks(I, od) == (2, 5, 6, 7)]
Y = (2, 5, 6, 7); P = Picks(I, Y); base = base_of_picks(I, Y)
print('sets', sets, 'vals', vals, 'orders giving picks', Y, ':', ords, 'F', P.F, 'D', P.D, 'J', P.J)
print('at the picks: one-absorber', extends_A(E, base, 1), ', S* owners', s_star_owners(I, base))
oa = ss = 0
for b2, ds in DF.moves(E, base, describe=True, all_desc=True).items():
    a = extends_A(E, b2, 1); s_ = s_star_owners(I, b2); oa += a; ss += bool(s_)
    if a:
        X = absorb_brute(I, b2, witness=True)
        print('  move', ds[0][:2], 'bundles', bundles_of(I, b2), 'frozen', frozen_set(I, b2), '| S* owners', s_, '| one-absorber completion', X)
print('one-move states with a one-absorber completion:', oa, '; with an S* completion:', ss)
