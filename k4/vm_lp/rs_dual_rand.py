"""The two RS-dual tests on random strict cores (k4/vm data loaders): python3 rs_dual_rand.py SOURCE"""
import sys, os, collections, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'vm'))
import rs_dual_full as F
one = F.one
from vm_test import items_for

if __name__ == '__main__':
    src = sys.argv[1]
    if len(sys.argv) > 2: F.DANGER[0] = sys.argv[2]
    jobs = [(sets, vals, name) for name, sets, vals, m in items_for(src)]
    print('$ python3 rs_dual_rand.py', src); print('instances', len(jobs), flush=True)
    T = collections.Counter(); B = []
    with mp.Pool(2) as pool:
        for C, bad in pool.imap_unordered(one, jobs, chunksize=20):
            T.update(C); B += bad
    for k, v in sorted(T.items(), key=str): print(' ', v, k)
    print('violations:', len(B))
    for b in B[:10]: print('  ', b)
