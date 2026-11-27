"""Frozen slots (coordinator's step 1; k4/oc1_hall.md §13).  At every distinct start: does the one-absorber completion
(SAT, k4/sdc/oc_absorb.extends_A: compensated frozen slots and any owner allowed) exist while the S* completion
(frozen agents take nothing; any owner, frozen owners included) does not?  For those starts: is S* restored by one
chain (Finding S*), and by a chain from a dangerous agent with k or the end owning (Finding B)?

    python3 k4/oc1_hall/frozen_slots.py SRC
"""
import sys, os, itertools, collections, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks
from chain_shapes import s_star_owners
from sdclib import Enc
from oc_absorb import extends_A
from min_frozen import load
import de_free as DF
DF.CHAIN_ONLY = True

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/oc1_hall/frozen_slots.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > 5: continue
        I = Inst(sets, vals, m, name); E = Enc(sets, vals, m); seen = set()
        for od in itertools.permutations(range(n)):
            Y = picks(I, od)
            if Y in seen: continue
            seen.add(Y); base = base_of_picks(I, Y)
            C['distinct starts'] += 1
            sat = extends_A(E, base, 1); ss = bool(s_star_owners(I, base))
            C['SAT %s, S* (any owner) %s' % (sat, ss)] += 1
            if sat and not ss:
                P = Picks(I, Y); B = False; anyc = False
                for b2, ds in DF.moves(E, base, describe=True, all_desc=True).items():
                    ow = s_star_owners(I, b2)
                    if not ow: continue
                    anyc = True
                    if any(d[1][0] in P.D and (d[1][0] in ow or d[1][-1] in ow) for d in ds): B = True; break
                C['  frozen-slot-only starts: S* restored by one chain %s, by a Finding-B chain %s' % (anyc, B)] += 1
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
