"""E5: the insertion step for a FIRST agent f from EVERY completion (k4/sd_induct.md §3).

For each start Y (one-absorber completion exists), each order pi producing Y and each level k (f = pi_k inserted into
I^{k+1} = (pi_{k+1}..pi_n)), and for EVERY X in A_{k+1}: the least Hamming distance from X to A_k (None if A_k is
empty).  Steps are classified by
  frozen  : some agent of I^{k+1} wants Y_f (v_i(Y_f) > v_i(Y_i), pick values)
  cur-frozen : some agent of I^{k+1} values Y_f above its value in X (current values; the condition that keeps f alone)
  thr     : f is threatened by X's absorber bundle (Lemma F)
and we test the explicit move 'f takes its best junk good of the absorber's bundle' (BEST) for the unfrozen case.

    python3 k4/sdind/e5_step.py special|screen|suite|cores:FILES:N:SEED [NMAX]"""
import sys, itertools, collections, json, time
import numpy as np
import _paths
from sdilib import Inst, sd, wanted_by, bundles_of, picks_base, efx0
from e1_delete import load
from e2_paths import sub_completions
from e3_suffix import absorber


def bestmove(I, Y, J, X, f, present):
    """X: assignment over J (agents of I); returns the assignment where f takes its most valuable junk good of the
    absorber's bundle (None if no absorber or f values none of them)"""
    o = absorber(X, I.n)
    if o is None: return None
    cand = [t for t in range(len(J)) if X[t] == o and I.V[f, J[t]] > 0]
    if not cand: return None
    t = max(cand, key=lambda t: (I.V[f, J[t]], -J[t]))
    X2 = X.copy(); X2[t] = f
    return X2


if __name__ == '__main__':
    src = sys.argv[1]; NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    C = collections.Counter(); t0 = time.time(); shown = collections.Counter()
    print('$ python3 k4/sdind/e5_step.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src):
        if len(sets) > NMAX or len(sets) < 2: continue
        I = Inst(sets, vals, m); C['instances'] += 1
        byY = collections.defaultdict(list)
        for o in itertools.permutations(range(I.n)):
            byY[tuple(sd(I, o)[0])].append(o)
        for Y, orders in byY.items():
            Y = list(Y); cache = {}
            try:
                full = sub_completions(I, Y, range(I.n), cache)
            except ValueError:
                continue
            if len(full) == 0: continue
            J = sorted(set(range(I.m)) - set(g for g in Y if g is not None))
            done = set()
            for pi in orders:
                seq = list(pi)[::-1]
                for k in range(1, I.n):
                    pres = tuple(sorted(seq[:k])); f = seq[k]
                    if (pres, f) in done: continue
                    done.add((pres, f))
                    P = sub_completions(I, Y, seq[:k], cache); Q = sub_completions(I, Y, seq[:k + 1], cache)
                    frozen = any(I.val(i, [Y[f]]) > I.val(i, [Y[i]] if Y[i] is not None else []) for i in pres) if Y[f] is not None else False
                    for X in P:
                        B = bundles_of(picks_base(I, Y), J, X)
                        cf = Y[f] is not None and any(I.val(i, [Y[f]]) > I.val(i, B[i]) for i in pres)
                        o = absorber(X, I.n)
                        vfp = int(I.V[f, Y[f]]) if Y[f] is not None else 0
                        thr = o is not None and (lambda vs: sum(vs) - min(vs) > vfp)([int(I.V[f, g]) for g in B[o]])
                        if len(Q) == 0: d = None
                        elif Q.shape[1] == 0: d = 0
                        else: d = int((Q != X[None, :]).sum(axis=1).min())
                        key = ('frozen' if frozen else 'unfrozen') + (' cur-frozen' if cf else ' cur-free') + (' thr' if thr else ' safe')
                        C[key + ': X'] += 1
                        C[key + ': least distance %s' % d] += 1
                        if not cf and thr:
                            X2 = bestmove(I, Y, J, X, f, pres)
                            ok = X2 is not None and len(Q) and (Q == X2[None, :]).all(axis=1).any()
                            C[key + ': BEST move works'] += bool(ok)
                            if not ok and shown[key] < 3:
                                shown[key] += 1
                                print('BEST FAILS', key, name, json.dumps((sets, vals)), 'picks', Y, 'present', pres, 'f', f,
                                      'X', dict(zip(J, X.tolist())), 'least d', d, flush=True)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
