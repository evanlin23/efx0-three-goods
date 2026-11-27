"""f = 2 hard starts (k4/oc1_hall.md §8): exactly two frozen agents x, y, and no S* completion at the picks.  Records:
  - the want relation between them (x wants y's pick, y wants x's, or neither) and |D|;
  - whether some unfrozen owner has a single culprit (deficit <= 0 once one frozen agent's demand is dropped);
  - for the repairing chains (de_free chain moves, all descriptions) with owner x_0 = k in D: whether the chain passes
    through the other frozen agent, unfreezes it (not frozen afterwards, off the chain), or leaves it frozen;
    whether it is canonical (no middle junk, each middle agent wants its predecessor's base).

    python3 k4/oc1_hall/f2_study.py SRC
"""
import sys, os, itertools, collections, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, bundles_of, frozen_set
from chain_shapes import s_star_owners
from culprit import deficits_without
from sdclib import Enc
from min_frozen import load
import de_free as DF
DF.CHAIN_ONLY = True

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/oc1_hall/f2_study.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > 5: continue
        I = Inst(sets, vals, m, name); E = Enc(sets, vals, m); seen = set()
        for od in itertools.permutations(range(n)):
            Y = picks(I, od)
            if Y in seen: continue
            seen.add(Y); P = Picks(I, Y)
            if len(P.F) != 2: continue
            base = base_of_picks(I, Y)
            if s_star_owners(I, base): continue
            x, y = P.F
            rel = ('x wants y' if x in P.W[y] else '') + (' y wants x' if y in P.W[x] else '')
            rel = rel.strip() or 'independent'
            if rel == 'y wants x': rel = 'x wants y'   # symmetric relabel
            C['hard f=2 starts'] += 1; C['  relation: %s, |D| = %d' % (rel, len(P.D))] += 1
            U = [o for o in range(n) if o not in P.F]
            single = any((deficits_without(I, base, r, {k}) or 99) <= 0 for r in U for k in P.F)
            C['  some owner with a single culprit'] += single
            feats = set()
            B = bundles_of(I, base)
            for b2, ds in DF.moves(E, base, describe=True, all_desc=True).items():
                ow = None
                for kind, path, H in ds:
                    k = path[0]
                    if k not in P.D: continue
                    if ow is None: ow = s_star_owners(I, b2)
                    if k not in ow: continue
                    other = y if k == x else x
                    F2 = set(frozen_set(I, b2))
                    if other in path: f = 'chain passes through the other frozen agent'
                    elif other not in F2: f = 'other frozen agent unfrozen off the chain'
                    else: f = 'other frozen agent stays frozen'
                    feats.add(f)
                    mid = any(H.get(i) for i in range(1, len(path)))
                    feats.add('canonical' if not mid and all(
                        B[path[i - 1]] and I.v[path[i]].get(B[path[i - 1]][0], 0) > P.pv[path[i]] for i in range(1, len(path)))
                        else 'not canonical')
                    feats.add('t = %d' % (len(path) - 1))
            for f in feats: C['  some owner-k repair: ' + f] += 1
            if not single: C['  no single culprit'] += 1
            if not single:
                for f in feats: C['  no single culprit, some owner-k repair: ' + f] += 1
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
