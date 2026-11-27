"""E14: which completion X' of the sub-instance to insert a both agent u into (free completions; k4/sd_induct.md §5).
Per case (Y, u): least distance over all X'; and for potentials Phi, whether EVERY maximizer of Phi on the free
completions of I - u - Y_u reaches a free completion of I with one move to u (u takes one junk good) or none.
  util      : sum of values
  -util     : minus the sum of values
  ujunk     : minus u's value of the junk goods lying in bundles of >= 3 goods (u's danger exposure)
  nlarge    : minus the number of junk goods in bundles of >= 3 goods
  leximin   : the sorted value vector, lexicographically (min first)
  holdval   : number of junk goods held by an agent that values them
  -holdval  : minus that
    python3 k4/sdind/e14_both_pot.py special|screen|suite|cores:FILES:N:SEED [NMAX]"""
import sys, itertools, collections, json, time
import numpy as np
import _paths
from sdilib import Inst, sd, wanted_by, completions, delete, picks_base, bundles_of
from e1_delete import load

POTS = ['util', '-util', 'ujunk', 'nlarge', 'leximin', 'holdval', '-holdval']

if __name__ == '__main__':
    src = sys.argv[1]; NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    C = collections.Counter(); t0 = time.time(); shown = collections.Counter()
    print('$ python3 k4/sdind/e14_both_pot.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src):
        if len(sets) > NMAX or len(sets) < 2: continue
        I = Inst(sets, vals, m); seen = set(); C['instances'] += 1
        for o_ in itertools.permutations(range(I.n)):
            Y = list(sd(I, o_)[0])
            if tuple(Y) in seen: continue
            seen.add(tuple(Y)); W = wanted_by(I, Y)
            both = [u for u in range(I.n) if Y[u] is not None and not W[u] and Y[u] == max(I.R[u], key=lambda h: (I.V[u, h], -h))]
            if not both: continue
            try:
                J, A = completions(I, picks_base(I, Y), None)
            except ValueError:
                continue
            Aset = set(map(tuple, A.tolist())); pb = picks_base(I, Y)
            for u in both:
                I2, amap, gmap = delete(I, [u], [Y[u]]); inv = {b: a for a, b in amap.items()}
                Y2 = [None] * I2.n
                for a, b in amap.items(): Y2[b] = gmap[Y[a]] if Y[a] is not None else None
                J2, A2 = completions(I2, picks_base(I2, Y2), None)
                if len(A2) == 0: continue
                C['cases'] += 1
                Xs = [np.array([inv[b] for b in x2], dtype=np.int64) for x2 in A2]
                def one_move(X):
                    if tuple(X.tolist()) in Aset: return True
                    for t in range(len(J)):
                        Z = X.copy(); Z[t] = u
                        if tuple(Z.tolist()) in Aset: return True
                    return False
                om = [one_move(X) for X in Xs]
                C['some X\' works with <= 1 move to u'] += any(om)
                C['every X\' works with <= 1 move to u'] += all(om)
                if not any(om) and shown['none'] < 3:
                    shown['none'] += 1; print('NO X\' WITH ONE MOVE', name, json.dumps((sets, vals)), 'picks', Y, 'u', u, flush=True)
                for P in POTS:
                    def phi(X):
                        B = bundles_of(pb, J, X)
                        vs = [I.val(i, B[i]) for i in range(I.n) if i != u]
                        if P == 'util': return sum(vs)
                        if P == '-util': return -sum(vs)
                        if P == 'ujunk': return -sum(int(I.V[u, g]) for t, g in enumerate(J) if len(B[X[t]]) >= 3)
                        if P == 'nlarge': return -sum(1 for t, g in enumerate(J) if len(B[X[t]]) >= 3)
                        if P == 'leximin': return tuple(sorted(vs))
                        if P == 'holdval': return sum(1 for t, g in enumerate(J) if I.V[X[t], g] > 0)
                        if P == '-holdval': return -sum(1 for t, g in enumerate(J) if I.V[X[t], g] > 0)
                    ph = [phi(X) for X in Xs]; best = max(ph)
                    ok = all(om[k] for k in range(len(Xs)) if ph[k] == best)
                    C['pot %s: every maximizer works' % P] += ok
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
