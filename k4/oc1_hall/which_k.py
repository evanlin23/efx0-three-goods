"""Which dangerous agent can start the repairing chain (k4/oc1_hall.md §6)?  At every hard start (no S* completion),
for every k in D: does some improving chain (k4/sdc/de_free.py chain moves) from x_0 = k leave an S* completion with
owner k (or with owner k or the chain end)?  Rules tested: every k in D; the first / last agent of D in the order pi;
the agent of D with the most wanters; the agent of D whose pick is most valuable to it.

    python3 k4/oc1_hall/which_k.py SRC
"""
import sys, os, itertools, collections, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks
from chain_shapes import s_star_owners
from sdclib import Enc
from min_frozen import load
import de_free as DF
DF.CHAIN_ONLY = True

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/oc1_hall/which_k.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > 5: continue
        I = Inst(sets, vals, m, name); E = Enc(sets, vals, m); seen = {}
        for od in itertools.permutations(range(n)):
            Y = picks(I, od)
            if Y in seen and seen[Y] is None: continue
            base = base_of_picks(I, Y)
            if Y not in seen:
                if s_star_owners(I, base): seen[Y] = None; continue
                P = Picks(I, Y); good = {k: set() for k in P.D}
                for b2, ds in DF.moves(E, base, describe=True, all_desc=True).items():
                    ow = None
                    for kind, path, H in ds:
                        k = path[0]
                        if k not in good: continue
                        if ow is None: ow = s_star_owners(I, b2)
                        if k in ow: good[k].add('k')
                        if path[-1] in ow or k in ow: good[k].add('k or end')
                seen[Y] = (P, good)
                C['hard starts'] += 1
                for pol in ('k', 'k or end'):
                    C['every k in D has a chain, owner %s' % pol] += all(pol in g for g in good.values())
                    C['some k in D has a chain, owner %s' % pol] += any(pol in g for g in good.values())
                    mw = max(P.D, key=lambda k: len(P.W[k]))
                    C['the k in D with most wanters (first such), owner %s' % pol] += pol in good[mw]
            P, good = seen[Y]
            C['hard (start, order) pairs'] += 1
            Dord = [i for i in od if i in P.D]
            for pol in ('k', 'k or end'):
                C['first agent of D in the order, owner %s' % pol] += pol in good[Dord[0]]
                C['last agent of D in the order, owner %s' % pol] += pol in good[Dord[-1]]
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
