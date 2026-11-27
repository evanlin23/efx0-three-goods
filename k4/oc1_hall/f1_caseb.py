"""f = 1, Case B (k4/oc1_hall.md §5): exactly one frozen agent x with top a = Y_x, wanters W, and for EVERY w in W
an improving set of x inside I(w) = (J + {Y_w}) & R_x.  For every such start (hard or not) and every swap (w, H_0)
with H_0 an inclusion-minimal improving set inside I(w), the owners that give an S* completion afterwards, by role:
x, w, another wanter, a non-wanter.  Sub-cases by |W|, n, the least |H_0|, and whether x values Y_w.

    python3 k4/oc1_hall/f1_caseb.py SRC
"""
import sys, os, itertools, collections, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks
from chain_shapes import s_star_owners
from f1_uncond import swaps
from min_frozen import load

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/oc1_hall/f1_caseb.py', *sys.argv[1:], flush=True)
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
            allsw = {w: swaps(I, P, base, x, w) for w in W}
            if not all(allsw.values()): continue
            hmin = min(len(H) for sw in allsw.values() for H, _ in sw)
            key = '|W|=%d n=%d min|H0|=%d' % (len(W), n, hmin)
            C['case B starts'] += 1; C[key + ': starts'] += 1
            roles = collections.Counter(); anyok = False
            for w, sw in allsw.items():
                for H0, nb in sw:
                    ow = s_star_owners(I, nb)
                    if ow: anyok = True
                    rs = set('x' if o == x else 'w' if o == w else 'other wanter' if o in W else 'non-wanter' for o in ow)
                    for r in rs: roles[r] += 1
            for r in roles: C[key + ': some swap, owner ' + r] += 1
            C[key + ': some swap works'] += anyok
            pc = bool(s_star_owners(I, base))
            C[key + ': picks complete'] += pc
            C[key + ': picks complete or some swap'] += pc or anyok
            C['case B: some swap works'] += anyok
            C['case B: picks complete or some swap'] += pc or anyok
            if not anyok and C['shown'] < 8:
                C['shown'] += 1
                print('CASE B, NO SWAP', name, json.dumps((sets, vals)), 'picks', Y, 'x', x, 'W', W, 'picks complete', pc, flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
