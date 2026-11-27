"""The starts where every canonical chain from k has HEAD (k4/oc1_hall.md §21; cross-check of proof/k4-d1's claim that
Finding D1 reduces to them, and that in the data they are n = 3, t = 1, f = 1 with two unfrozen wanters of Y_k).
At every one-absorber-hard start with D = {k}: whether some canonical chain from k (unfrozen head) has no HEAD
(HEAD is a property of the path); for the starts where none has, print n, the chain lengths, f, |W_k| and the
wanters' frozen status, and whether some chain with a minimal H_0 still repairs.

    python3 k4/oc1_hall/d1_allhead.py SRC
"""
import sys, os, itertools, collections, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks
from greedy_rules import canonical_paths
from d1_subcases import analyse
from sdclib import Enc
from oc_absorb import extends_A
from min_frozen import load

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter()
    print('$ python3 k4/oc1_hall/d1_allhead.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > 5: continue
        I = Inst(sets, vals, m, name); E = Enc(sets, vals, m); seen = set()
        for od in itertools.permutations(range(n)):
            Y = picks(I, od)
            if Y in seen: continue
            seen.add(Y); P = Picks(I, Y)
            if len(P.D) != 1: continue
            base = base_of_picks(I, Y)
            if extends_A(E, base, 1): continue
            k = P.D[0]; C['starts'] += 1; heads = {}; rep = False
            for path in canonical_paths(I, P, k):
                if path[-1] in P.F: continue
                xt = path[-1]; Pi = list(P.J) + ([Y[xt]] if Y[xt] is not None else []); Pik = [g for g in Pi if g in I.R[k]]
                imp = [H for r in range(1, len(Pik) + 1) for H in itertools.combinations(Pik, r) if I.val(k, H) > P.pv[k]]
                mins = [H for H in imp if not any(set(K) < set(H) for K in imp)]
                res = [analyse(I, P, base, k, path, H0) for H0 in mins]
                heads[path] = any('HEAD' in r[0] for r in res)
                rep |= any(r[1] is not None for r in res)
            if heads and all(heads.values()):
                key = 'n=%d t=%s f=%d |W_k|=%d wanters unfrozen=%s' % (n, sorted({len(p) - 1 for p in heads}), len(P.F), len(P.W[k]),
                                                                      all(w not in P.F for w in P.W[k]))
                C['starts where every canonical chain has HEAD'] += 1; C['  ' + key] += 1; C['  ... and some chain repairs'] += rep
                print('ALL-HEAD', name, json.dumps((sets, vals)), 'order', od, 'picks', Y, 'k', k, key, 'repaired', rep, flush=True)
    for k_ in sorted(C): print(k_, C[k_])
