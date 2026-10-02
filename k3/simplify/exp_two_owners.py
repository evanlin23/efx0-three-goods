"""In K3ALG's bad case (r not a valid owner), is there an EFX0 completion of the SAME pre-allocation (no rotation)
with two absorbers r and t (t another terminal)? Junk goes into slots (at most cap(i) per other terminal) or to r or t
(any number). Exhaustive search over junk placements."""
import sys, os, collections, multiprocessing, itertools
sys.path.insert(0, os.path.dirname(__file__))
from lbx import State, LEADERS, core_profiles, efx0, owner_step

def two_owner_completion(st, Y, U, r, any_owner=False):
    J = st.junk(Y, U); cap = st.caps(Y, U)
    base = [None] * st.m
    for i in range(st.n):
        if Y[i] is not None: base[Y[i]] = i
    for u in U: base[st.rank[u][2]] = u
    terms = [i for i in range(st.n) if cap[i] > 0]
    owners1 = terms + list(U) if any_owner else [r]
    for o1 in owners1:
        for t in [i for i in terms + list(U) if i != o1]:
            recips = sorted(set(terms) | {o1, t})
            for asg in itertools.product(recips, repeat=len(J)):
                cnt = collections.Counter(asg)
                if any(cnt[i] > cap[i] for i in recips if i not in (o1, t)): continue
                X = list(base)
                for g, i in zip(J, asg): X[g] = i
                if efx0(st.rank, st.m, X): return (o1, t, X)
    return None

def work(args):
    n, m, rank = args
    st = State(rank, m); order, Y, blk, _ = st.phase1(LEADERS['index']); U = st.upgrades(Y, [])
    tag, r = owner_step(st, Y, U, order, blk)
    if tag != 'bad': return n, None, None
    res = two_owner_completion(st, Y, U, r)
    return n, res is not None, (rank, m)

if __name__ == '__main__':
    maxn = int(sys.argv[1]); sample = int(sys.argv[2]) if len(sys.argv) > 2 else 0; minn = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    c = collections.Counter(); ex = None
    with multiprocessing.Pool(4) as pool:
        for n, ok, inst in pool.imap_unordered(work, core_profiles(maxn, sample=sample, minn=minn), chunksize=500):
            if ok is None: continue
            c[(n, ok)] += 1
            if not ok and ex is None: ex = inst
    print("bad cases (n, has a 2-absorber completion without rotation):", dict(sorted(c.items())))
    if ex: print("first bad case without one:", ex)
