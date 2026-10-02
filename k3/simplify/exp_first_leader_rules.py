"""Which first leader avoids the rotation? Candidates named by their role in the failed index run, or by features."""
import sys, os, collections, multiprocessing, random
sys.path.insert(0, os.path.dirname(__file__))
from k3s import k3s
from lbx import core_profiles
from test_k3s import gen_small
from exp_first_leader import with_first

def failed_run_roles(n, m, rank):
    """re-derive k*, the chain and r of the index run (K3S's rotation step)"""
    v = [dict(zip(r, (4, 3, 2))) for r in rank]
    info = {}; k3s(n, m, v, info)          # with rotation: records chain via a small hack below
    return info

def work(a):
    n, m, rank = a
    v = [dict(zip(r, (4, 3, 2))) for r in rank]
    info = {}
    if k3s(n, m, v, info, rotate=False) is not None: return None
    leaders = info['leaders']
    ok = {x for x in range(n) if k3s(n, m, v, leader=with_first(x), rotate=False) is not None}
    info2 = {}; k3s(n, m, v, info2)
    tops = collections.Counter(r[0] for r in rank)
    valued = collections.Counter(g for r in rank for g in r)
    feats = {
        'k* (last leader)': leaders[-1],
        'first leader of the index run': leaders[0],
        'second leader of the index run': leaders[1] if len(leaders) > 1 else None,
        'chain x1': info2.get('chain', [None, None])[1] if len(info2.get('chain', [])) > 1 else None,
        'r of the index run': info2.get('r'),
        'most-claimed top (then index)': max(range(n), key=lambda x: (valued[rank[x][0]], -x)),
        'least-claimed top (then index)': min(range(n), key=lambda x: (valued[rank[x][0]], x)),
        'b and c most valued': max(range(n), key=lambda x: (valued[rank[x][1]] + valued[rank[x][2]], -x)),
        'b or c is a top (most)': max(range(n), key=lambda x: ((rank[x][1] in tops) + (rank[x][2] in tops), -x)),
        'last agent index': n - 1,
    }
    return {k: (x is not None and x in ok) for k, x in feats.items()}, len(ok), n

def run(src, label):
    tot = 0; c = collections.Counter(); frac = 0
    with multiprocessing.Pool(4) as pool:
        for res in pool.imap_unordered(work, src, chunksize=300):
            if res is None: continue
            d, k, n = res; tot += 1; frac += k / n
            for key, ok in d.items(): c[key] += ok
    print(f"{label}: {tot} profiles need a rotation; on average {frac / max(tot, 1):.2f} of the agents work as first leader")
    for key in c: print(f"   {key:34s} works on {c[key]} / {tot}")

if __name__ == '__main__':
    run(core_profiles(4), "cores n <= 4")
    run(core_profiles(5, sample=300, minn=5), "cores n = 5 (300 per core)")
    run(gen_small(3, 6), "all profiles n=3 m=6")
