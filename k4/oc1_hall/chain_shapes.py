"""Which chains repair under the shape S* (k4/oc1_hall.md §2: owner any agent; one junk good each for unfrozen
single-good holders; nothing for frozen agents and multi-good holders).  For every distinct hard start (picks with no
S* completion), every repairing chain (k4/sdc/de_free.py chain moves, all descriptions) and every working owner, record
features; then count the starts having some repairing (chain, owner) with each property.

    python3 k4/oc1_hall/chain_shapes.py special|screen|suite|logs|cores:FILES N SEED
"""
import sys, os, itertools, collections, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, bundles_of, frozen_set, shaped_completion
from sdclib import Enc
from min_frozen import load
import de_free as DF
DF.CHAIN_ONLY = True
NMAX = int(os.environ.get('NMAX', '5'))


def s_star_owners(I, base):
    B = bundles_of(I, base); F = set(frozen_set(I, base))
    holders = [j for j in range(I.n) if len(B[j]) <= 1 and j not in F]
    return [o for o in range(I.n) if shaped_completion(I, base, o, holders)]


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/oc1_hall/chain_shapes.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > NMAX: continue
        I = Inst(sets, vals, m, name); E = Enc(sets, vals, m); seen = set()
        for od in itertools.permutations(range(n)):
            Y = picks(I, od)
            if Y in seen: continue
            seen.add(Y); base = base_of_picks(I, Y)
            if s_star_owners(I, base): continue
            P = Picks(I, Y); C['hard starts'] += 1
            C['hard starts with |F| = %d, |D| = %d' % (len(P.F), len(P.D))] += 1
            feats = collections.Counter(); B = bundles_of(I, base)
            for b2, ds in DF.moves(E, base, describe=True, all_desc=True).items():
                owners = s_star_owners(I, b2)
                if not owners: continue
                for kind, path, H in ds:
                    x0, xt = path[0], path[-1]; t = len(path) - 1
                    mid_junk = any(H.get(i) for i in range(1, len(path)))
                    canon = (t >= 1 and not mid_junk and
                             all(I.v[path[i]].get(B[path[i - 1]][0], 0) > P.pv[path[i]] if B[path[i - 1]] else False
                                 for i in range(1, len(path))))
                    H0 = H.get(0, ()); from_end = t >= 1 and any(g in B[xt] for g in H0)
                    canon = canon and (not P.W[xt] or from_end)
                    f = set()
                    f.add('x0 frozen' if x0 in P.F else 'x0 unfrozen')
                    if x0 in P.D: f.add('x0 dangerous')
                    if not mid_junk: f.add('no middle junk')
                    if canon: f.add('canonical (x0 -> wanters, no middle junk; end unwanted or its pick to x0)')
                    if canon and x0 in P.D: f.add('canonical from D')
                    if t == 1: f.add('t = 1 (swap)')
                    f.add('|H0| = %d' % len(H0))
                    if from_end: f.add('x0 takes a good of the end')
                    for o in owners:
                        role = 'x0' if o == x0 else ('end' if o == xt else ('middle' if o in path else 'off chain'))
                        g = set(f); g.add('owner ' + role)
                        if canon and x0 in P.D: g.add('canonical from D, owner ' + role)
                        if canon and x0 in P.D and not from_end: g.add('canonical from D, junk only, owner ' + role)
                        if x0 in P.D: g.add('x0 in D, owner ' + role)
                        for z in g: feats[z] += 1
                    if canon and x0 in P.D and x0 in owners: f.add('canonical from D, owner x0')
            for z in feats: C['  some repair: ' + z] += 1
            if not any('canonical from D' == z for z in feats) and C['shown'] < 5:
                C['shown'] += 1
                print('NO CANONICAL-FROM-D REPAIR', name, json.dumps((sets, vals)), 'picks', Y, 'F', P.F, 'D', P.D, flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
