"""Mechanisms for f = 1 (k4/oc1_hall.md §5).  For every start with exactly one frozen agent x (top a = Y_x, wanters W,
L_x = x's other goods), record which of these give an S* completion:
  T2+ : some o != x with v_x((J + {Y_o}) & R_x) <= p_x  (then owner o, nothing kept out; proved, Prop. 3);
  PK1 : picks, an unfrozen owner, deficit <= 0 with |H| <= 1 (ohlib.deficit's least H);
  PK  : picks, an unfrozen owner (deficit <= 0);
  PKF : picks, a frozen owner (x);
  SWo : a swap (w, minimal H_0) with an owner outside {x, w};
  SWx : a swap with owner x;   SWw : a swap with owner w;
and print the starts covered by none of T2+, PK, SWo, SWx (with |W|, n).

    python3 k4/oc1_hall/f1_mech.py SRC
"""
import sys, os, itertools, collections, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, s_star_deficits
from chain_shapes import s_star_owners
from f1_uncond import swaps
from min_frozen import load

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/oc1_hall/f1_mech.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > 5: continue
        I = Inst(sets, vals, m, name); seen = set()
        for od in itertools.permutations(range(n)):
            Y = picks(I, od)
            if Y in seen: continue
            seen.add(Y); P = Picks(I, Y)
            if len(P.F) != 1: continue
            x = P.F[0]; W = P.W[x]; base = base_of_picks(I, Y)
            key = '|W|=%d n=%d' % (min(len(W), 2), n)
            C[key + ': starts'] += 1
            t2 = any(I.val(x, [g for g in P.J + [Y[o]] if g is not None and g in I.R[x]]) <= P.pv[x] for o in range(n) if o != x)
            mech = set()
            if t2: mech.add('T2+')
            U = [o for o in range(n) if o != x]
            d = s_star_deficits(I, base, U)
            if any(d[o][0] is not None and d[o][0] <= 0 for o in U): mech.add('PK')
            if any(d[o][0] is not None and d[o][0] <= 0 and len(d[o][1]) <= 1 for o in U): mech.add('PK1')
            if x in s_star_owners(I, base): mech.add('PKF')
            for w in W:
                for H0, nb in swaps(I, P, base, x, w):
                    ow = s_star_owners(I, nb)
                    if set(ow) - {x, w}: mech.add('SWo')
                    if x in ow: mech.add('SWx')
                    if w in ow: mech.add('SWw')
            for z in mech: C[key + ': ' + z] += 1
            rest = mech & {'T2+'}
            C[key + ': none of T2+'] += not mech & {'T2+'}
            C[key + ': none of T2+, PK1'] += not mech & {'T2+', 'PK1'}
            C[key + ': none of T2+, PK1, SWo'] += not mech & {'T2+', 'PK1', 'SWo'}
            C[key + ': none of T2+, PK1, SWo, SWx'] += not mech & {'T2+', 'PK1', 'SWo', 'SWx'}
            C[key + ': none of T2+, PK, SWo, SWx'] += not mech & {'T2+', 'PK', 'SWo', 'SWx'}
            if not mech & {'T2+', 'PK1', 'SWo', 'SWx'} and C['shown'] < 10:
                C['shown'] += 1
                print('UNCOVERED', key, name, json.dumps((sets, vals)), 'picks', Y, 'x', x, 'W', W, sorted(mech), flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
