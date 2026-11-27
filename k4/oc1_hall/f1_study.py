"""The f = 1 hard starts under the shape S* (k4/oc1_hall.md §3): picks with exactly one frozen agent x and no S*
completion.  For each: |W| (wanters of Y_x), x's junk, and the repairing swaps x -> w (x takes H_0 from J + {Y_w}, w
takes Y_x), with the owners that work afterwards.  Counts which (wanter, H_0, owner) rules always work.

    python3 k4/oc1_hall/f1_study.py SRC [VERBOSE]
"""
import sys, os, itertools, collections, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, bundles_of
from chain_shapes import s_star_owners
from min_frozen import load
from dump_hard import describe

if __name__ == '__main__':
    src = sys.argv[1]; VERB = len(sys.argv) > 2 and sys.argv[2] == 'v'; C = collections.Counter(); t0 = time.time()
    argv = [a for a in sys.argv if a != 'v']
    print('$ python3 k4/oc1_hall/f1_study.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src, argv):
        n = len(sets)
        if n > 5: continue
        I = Inst(sets, vals, m, name); seen = set()
        for od in itertools.permutations(range(n)):
            Y = picks(I, od)
            if Y in seen: continue
            seen.add(Y); P = Picks(I, Y)
            if len(P.F) != 1: continue
            base = base_of_picks(I, Y)
            if s_star_owners(I, base): continue
            x = P.F[0]; W = P.W[x]; key = '|W|=%d' % len(W)
            C[key + ' hard starts'] += 1
            res = []   # (w, H0, value, owners)
            for w in W:
                pool = [g for g in P.J if g in I.R[x]] + ([Y[w]] if Y[w] is not None and Y[w] in I.R[x] else [])
                for r in range(1, len(pool) + 1):
                    for H0 in itertools.combinations(pool, r):
                        if I.val(x, H0) <= P.pv[x]: continue
                        nb = list(base); nb[Y[x]] = w
                        if Y[w] is not None: nb[Y[w]] = -1
                        for g in H0: nb[g] = x
                        res.append((w, H0, I.val(x, H0), s_star_owners(I, tuple(nb))))
            ok = [r for r in res if r[3]]
            C[key + ' some swap repairs'] += bool(ok)
            C[key + ' some swap repairs with owner x'] += any(x in r[3] for r in ok)
            C[key + ' some swap repairs with owner w'] += any(r[0] in r[3] for r in ok)
            # minimal H0 (inclusion-minimal improving sets)
            minimal = [r for r in res if not any(set(s[1]) < set(r[1]) and s[0] == r[0] for s in res)]
            C[key + ' some minimal-H0 swap repairs'] += any(r[3] for r in minimal)
            C[key + ' some minimal-H0 swap repairs, owner x'] += any(x in r[3] for r in minimal)
            C[key + ' every minimal-H0 swap repairs, owner x'] += all(x in r[3] for r in minimal)
            # x's full set: every good it values in J + {Y_w}
            full = {}
            for r in res:
                if r[0] not in full or len(r[1]) > len(full[r[0]][1]): full[r[0]] = r
            C[key + ' some wanter repairs with x taking everything (owner x)'] += any(x in r[3] for r in full.values())
            C[key + ' every wanter repairs with x taking everything (owner x)'] += all(x in r[3] for r in full.values())
            if (VERB and C[key + ' shown'] < 4) or not ok:
                C[key + ' shown'] += 1
                print('F1 HARD', name, json.dumps((sets, vals)), 'picks', Y, 'x', x, 'W', W, 'J', P.J)
                print(describe(I, P))
                for r in res: print('   swap to %d H0 %s (%d) owners %s' % r)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
