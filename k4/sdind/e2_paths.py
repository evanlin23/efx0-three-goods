"""E2: paths of completions along a growing set of agents (k4/sd_induct.md §1).

For an SD outcome Y with junk J and a set U of agents, I_U = (agents U, goods Y[U] + J).  Y restricted to U is an SD
outcome of I_U (pi restricted to U) and the junk is J for every U.  A(U) = one-absorber EFX0 completions of I_U,
i.e. maps J -> U.  An insertion sequence u_1, ..., u_n adds one agent at a time.  A *path* is X_1 in A({u_1}), ...,
X_n in A(N) with Hamming distance d(X_{k-1}, X_k) <= d at every step.  Questions per start:
  * prefix order (u = pi, i.e. delete the LAST agent each time going down): is every A(U) nonempty?  least d?
  * suffix order (u = reverse pi, delete the FIRST agent going down): same;
  * best insertion sequence over all n! sequences (any agent can be deleted: the SD-consistency holds for every u).
Here pi is the lexicographically first order producing Y, and also every order producing Y is tried for 'some
order of pi' counts.

    python3 k4/sdind/e2_paths.py special|screen|suite|cores:FILES:N:SEED [NMAX]"""
import sys, itertools, collections, json, time
import numpy as np
import _paths
from sdilib import Inst, sd, completions, delete, picks_base, wanted_by
from e1_delete import load


def sub_completions(I, Y, U, cache):
    U = tuple(sorted(U))
    if U in cache: return cache[U]
    rest = [i for i in range(I.n) if i not in U]
    gone = [Y[i] for i in rest if Y[i] is not None]
    I2, amap, gmap = delete(I, rest, gone)
    inv = {b: a for a, b in amap.items()}
    Y2 = [None] * I2.n
    for a, b in amap.items(): Y2[b] = gmap[Y[a]] if Y[a] is not None else None
    J2, A2 = completions(I2, picks_base(I2, Y2), 1)
    A2 = np.vectorize(lambda b: inv[b], otypes=[np.int64])(A2) if A2.size else A2.reshape(len(A2), len(J2))
    cache[U] = A2
    return A2


def bottleneck(levels):
    """least d such that a path with all steps <= d exists through the levels (lists of assignment arrays); None if
    some level is empty"""
    if any(len(L) == 0 for L in levels): return None
    best = np.zeros(len(levels[0]), dtype=np.int64)   # best bottleneck to reach each element
    for k in range(1, len(levels)):
        P, Q = levels[k - 1], levels[k]
        if P.shape[1] == 0:
            best = np.zeros(len(Q), dtype=np.int64); continue
        D = (P[:, None, :] != Q[None, :, :]).sum(axis=2)  # (|P|, |Q|)
        best = np.maximum(D, best[:, None]).min(axis=0)
    return int(best.min())


if __name__ == '__main__':
    src = sys.argv[1]; NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    C = collections.Counter(); t0 = time.time(); shown = collections.Counter()
    print('$ python3 k4/sdind/e2_paths.py', *sys.argv[1:], flush=True)
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
            C['starts (one-absorber completion exists)'] += 1
            for kind in ('prefix', 'suffix'):
                vals_d = []
                for o in orders:
                    seq = list(o) if kind == 'prefix' else list(o)[::-1]
                    levels = [sub_completions(I, Y, seq[:k], cache) for k in range(1, I.n + 1)]
                    vals_d.append(bottleneck(levels))
                o0 = vals_d[0]
                C['%s, first order: least d %s' % (kind, o0)] += 1
                okd = [d for d in vals_d if d is not None]
                C['%s, best order of Y: least d %s' % (kind, min(okd) if okd else None)] += 1
                if o0 is None and shown[kind] < 3:
                    shown[kind] += 1
                    print('EMPTY LEVEL', kind, name, json.dumps((sets, vals)), 'picks', Y, 'order', orders[0], flush=True)
            # best insertion sequence over all n!
            bestd = None
            for seq in itertools.permutations(range(I.n)):
                levels = [sub_completions(I, Y, seq[:k], cache) for k in range(1, I.n + 1)]
                d = bottleneck(levels)
                if d is not None and (bestd is None or d < bestd): bestd = d
            C['any insertion sequence: least d %s' % bestd] += 1
            # every subset nonempty?
            allU = all(len(sub_completions(I, Y, U, cache)) > 0 for r in range(1, I.n + 1)
                       for U in itertools.combinations(range(I.n), r))
            C['every sub-instance I_U has a one-absorber completion'] += allU
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
