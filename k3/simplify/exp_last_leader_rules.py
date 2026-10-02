"""When K3S (index leaders) would rotate, redo the draft with the LAST insertion step's leader replaced by a named
agent of the failed run: x1 (the first agent of the need chain from k*, which needed k*'s top) or r."""
import sys, os, collections, multiprocessing, random
sys.path.insert(0, os.path.dirname(__file__))
from k3s import k3s
from lbx import core_profiles
from test_k3s import gen_small
from exp_first_leader import with_step

def work(a):
    n, m, rank = a
    v = [dict(zip(r, (4, 3, 2))) for r in rank]
    info = {}
    if k3s(n, m, v, info, rotate=False) is not None: return None
    L = len(info['leaders']); info2 = {}; k3s(n, m, v, info2)
    x1, r = info2['chain'][1], info2['r']
    return tuple(k3s(n, m, v, leader=with_step(L - 1, y), rotate=False) is not None for y in (x1, r)), (rank, m)

def run(src, label):
    c = collections.Counter(); ex = {}
    with multiprocessing.Pool(4) as pool:
        for res in pool.imap_unordered(work, src, chunksize=500):
            if res is None: continue
            (a, b), inst = res; c['n'] += 1; c['x1'] += a; c['r'] += b
            if not a: ex.setdefault('x1', inst)
            if not b: ex.setdefault('r', inst)
    print(f"{label}: need rotation {c['n']}; last leader := x1 works {c['x1']}; := r works {c['r']}", ex, flush=True)

if __name__ == '__main__':
    run(core_profiles(5), "every core profile n <= 5")
    for n, m in [(3, 6), (3, 7), (4, 5)]: run(gen_small(n, m), f"every ranking profile n={n} m={m}")
