"""Is it enough to choose only the FIRST leader (all later leaders by index)? Or only the LAST insertion step?
Counts, among profiles where K3S with index leaders needs a rotation, those where some choice works."""
import sys, os, collections, multiprocessing
sys.path.insert(0, os.path.dirname(__file__))
from k3s import k3s
from lbx import core_profiles
from test_k3s import gen_small

def with_first(x):
    state = {'first': True}
    def lead(ctx, unproc, free, Y):
        if state['first']:
            state['first'] = False
            if x in unproc: return x
        return unproc[0]
    return lead

def nins(n, m, v):
    info = {}; k3s(n, m, v, info, rotate=False); return len(info.get('leaders', []))

def with_step(t, x):
    state = {'k': 0}
    def lead(ctx, unproc, free, Y):
        k = state['k']; state['k'] += 1
        return x if (k == t and x in unproc) else unproc[0]
    return lead

def work(a):
    n, m, rank = a
    v = [dict(zip(r, (4, 3, 2))) for r in rank]
    if k3s(n, m, v, rotate=False) is not None: return None
    first_ok = [x for x in range(n) if k3s(n, m, v, leader=with_first(x), rotate=False) is not None]
    L = nins(n, m, v)
    last_ok = [x for x in range(n) if k3s(n, m, v, leader=with_step(L - 1, x), rotate=False) is not None]
    return bool(first_ok), bool(last_ok), (rank, m)

def run(src, label):
    c = collections.Counter(); ex = {}
    with multiprocessing.Pool(4) as pool:
        for res in pool.imap_unordered(work, src, chunksize=500):
            if res is None: continue
            f, l, inst = res; c['total'] += 1; c['first'] += f; c['last'] += l
            if not f: ex.setdefault('first', inst)
            if not l: ex.setdefault('last', inst)
    print(f"{label}: need rotation {c['total']}; fixed by choosing the first leader {c['first']}; by the last {c['last']}", ex, flush=True)

if __name__ == '__main__':
    run(core_profiles(4), "cores n <= 4")
    for n, m in [(3, 4), (3, 5), (3, 6), (3, 7)]: run(gen_small(n, m), f"all profiles n={n} m={m}")
    run(core_profiles(5, sample=300, minn=5), "cores n = 5 (300 per core)")
