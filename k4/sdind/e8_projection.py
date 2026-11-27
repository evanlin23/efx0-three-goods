"""E8: projections of a final completion (k4/sd_induct.md §3).  For a completion X* in A(N) with absorber o (an
agent with >= 2 junk goods; if none, every agent not frozen is tried as o), and a set U of agents containing o, the
projection X*|U gives every junk good to its X*-holder if that holder is in U, else to o.  Inserting an agent f moves
only f's own junk (at most one good) from o to f, so projections along a suffix insertion have steps <= 1.  The
projection X*|U is EFX0 for I_U iff no agent of U is threatened by o's inflated bundle (the other bundles are final).
Question: for every X*, is there an insertion order (o first, then the reverse of an order producing Y) along which
every projection is EFX0?  And for some X*?

    python3 k4/sdind/e8_projection.py special|screen|suite|cores:FILES:N:SEED [NMAX]"""
import sys, itertools, collections, json, time
import numpy as np
import _paths
from sdilib import Inst, sd, wanted_by, bundles_of, picks_base, threatened
from e1_delete import load
from e2_paths import sub_completions
from e3_suffix import absorber


def proj_ok(I, Y, J, X, o, U):
    Xp = np.array([x if x in U else o for x in X], dtype=np.int64)
    B = bundles_of(picks_base(I, Y), J, Xp)
    Ul = sorted(U)
    for i in Ul:
        if i == o: continue
        own = I.val(i, B[i]); vs = [int(I.V[i, g]) for g in B[o]]
        if vs and sum(vs) - min(vs) > own: return False
    return True


def schedulable(I, Y, J, X, o, W):
    """DFS over insertion orders: o first; f can be inserted when all its wanted agents... (constraint: if i wants
    Y_j then i is inserted before j) and the projection after inserting f is EFX0 (only f's safety and the others'
    safety against the shrunken o-bundle matter; o-bundle only shrinks, so only f needs checking -- we check all)"""
    n = I.n
    wants = {i: set(j for j in range(n) if i in W[j]) for i in range(n)}   # i wants Y_j
    wanters = {j: set(W[j]) for j in range(n)}
    if wanters[o]: return False
    seen = set()
    def rec(U):
        if len(U) == n: return True
        if U in seen: return False
        seen.add(U)
        for f in range(n):
            if f in U or not wanters[f] <= U: continue
            U2 = U | {f}
            if proj_ok(I, Y, J, X, o, U2) and rec(U2): return True
        return False
    return rec(frozenset([o])) if proj_ok(I, Y, J, X, o, {o}) else False


if __name__ == '__main__':
    src = sys.argv[1]; NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    C = collections.Counter(); t0 = time.time(); shown = collections.Counter()
    print('$ python3 k4/sdind/e8_projection.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src):
        if len(sets) > NMAX or len(sets) < 2: continue
        I = Inst(sets, vals, m); C['instances'] += 1
        seenY = set()
        for o_ in itertools.permutations(range(I.n)):
            Y = list(sd(I, o_)[0])
            if tuple(Y) in seenY: continue
            seenY.add(tuple(Y)); cache = {}
            try:
                full = sub_completions(I, Y, range(I.n), cache)
            except ValueError:
                continue
            if len(full) == 0: continue
            C['starts'] += 1
            J = sorted(set(range(I.m)) - set(g for g in Y if g is not None))
            W = wanted_by(I, Y)
            res = []
            for X in full:
                o = absorber(X, I.n)
                os_ = [o] if o is not None else [i for i in range(I.n) if not W[i]]
                res.append(any(schedulable(I, Y, J, X, oo, W) for oo in os_))
            C['completions'] += len(res); C['completions schedulable'] += sum(res)
            C['starts: every completion schedulable'] += all(res)
            C['starts: some completion schedulable'] += any(res)
            if not any(res) and shown['none'] < 3:
                shown['none'] += 1; print('NO SCHEDULABLE COMPLETION', name, json.dumps((sets, vals)), 'picks', Y, flush=True)
            if not all(res) and shown['notall'] < 3:
                shown['notall'] += 1
                X = full[res.index(False)]
                print('UNSCHEDULABLE COMPLETION', name, json.dumps((sets, vals)), 'picks', Y, 'X', dict(zip(J, X.tolist())), flush=True)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
