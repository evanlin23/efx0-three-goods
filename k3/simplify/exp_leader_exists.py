"""For profiles where K3S (index leaders) needs a rotation: does SOME sequence of leader choices avoid it?
  r-valid : with the absorber r (K3S's rule)
  any-abs : with the best absorber (any free or upgraded agent; HitSet test exact by brute force)"""
import sys, os, itertools, collections, multiprocessing
sys.path.insert(0, os.path.dirname(__file__))
from k3s import k3s, efx0
from lbx import core_profiles
from test_k3s import gen_small

def runs_all_leaders(n, m, v):
    """yield (absorbed-by-r ok, any-absorber ok) for every sequence of leader choices"""
    def rec(seq):
        it = iter(seq); used = []
        def lead(ctx, unproc, free, Y):
            x = next(it, None)
            if x is None or x not in unproc: raise LookupError(list(unproc))
            used.append(x); return x
        try:
            info = {}; X = k3s(n, m, v, info, leader=lead, rotate=False)
            yield seq, X is not None
        except LookupError as e:
            for x in e.args[0]: yield from rec(seq + [x])
    yield from rec([])

def work(a):
    n, m, rank = a
    v = [dict(zip(r, (4, 3, 2))) for r in rank]; info = {}
    if k3s(n, m, v, info, rotate=False) is not None: return None
    ok = [s for s, good in runs_all_leaders(n, m, v) if good]
    return n, bool(ok), (rank, m)

def run(src, label):
    c = collections.Counter(); ex = None
    with multiprocessing.Pool(4) as pool:
        for res in pool.imap_unordered(work, src, chunksize=500):
            if res is None: continue
            n, ok, inst = res; c[ok] += 1
            if not ok and ex is None: ex = inst
    print(f"{label}: profiles needing a rotation with index leaders: {sum(c.values())}; some leader sequence avoids it: {c[True]}; none does: {c[False]}", ex or "", flush=True)

if __name__ == '__main__':
    run(core_profiles(4), "cores n <= 4")
    for n, m in [(3, 4), (3, 5), (3, 6), (3, 7)]: run(gen_small(n, m), f"all profiles n={n} m={m}")
    run(core_profiles(5, sample=100, minn=5), "cores n = 5 (100 per core)")
