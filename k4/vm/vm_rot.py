"""How many rotations the rotation class needs (k4/vm.md section 7.6).  For every instance of vm_classify's class
'rotation', over every V-M matching Y and every F1-with-rotation placement sequence from Y (DFS, capped): the least
number of envy-cycle rotations on a successful run, the lengths of the rotated cycles, and whether the first rotation
happens before every agent frozen at Y is unfrozen.  EVIDENCE only.
    python3 k4/vm/vm_rot.py SOURCE"""
import sys, os, collections, json, time, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
from vm_test import items_for
from vm_extend import Enc
from vm_classify import classify, ORDER


def rotate_count(I, X):
    """rotate envy cycles (as l3_source) and return the list of rotated cycle lengths"""
    lens = []
    while True:
        E = V.envy_graph(I, X); cyc = V.find_cycle(E, I.n)
        if cyc is None: return lens
        B = [list(X[c]) for c in cyc]
        for t, c in enumerate(cyc): X[c] = B[(t + 1) % len(cyc)]
        lens.append(len(cyc))


def one(args):
    name, sets, vals, m = args
    I = V.Inst(sets, vals, m); E = Enc(sets, vals, m)
    if ORDER[classify(I, E)] != 'rotation': return None
    best = None
    for ch, r in V.all_runs(V.vm_run, I, stop='II'):
        if isinstance(r, V.Stuck): continue
        stack = [([list(b) for b in r[0]], [])]; leaves = 0
        while stack and leaves < 50000:
            X, rots = stack.pop(); rots = rots + rotate_count(I, X)
            pool = set(range(m)) - set(g for b in X for g in b); valued = sorted(g for g in pool if I.valued_by(g))
            if not valued:
                leaves += 1
                if best is None or (len(rots), rots) < (len(best), best): best = rots
                continue
            br = False
            for g in valued:
                for s in range(I.n):
                    if V.safe_add(I, X, s, g):
                        Z = [list(b) for b in X]; Z[s].append(g); stack.append((Z, rots)); br = True
            if not br: leaves += 1
    return name, I.n, I.m, best


if __name__ == '__main__':
    src = sys.argv[1]; print('$ python3 k4/vm/vm_rot.py', ' '.join(sys.argv[1:]))
    C = collections.Counter(); rows = []
    with mp.Pool(os.cpu_count()) as pool:
        for res in pool.imap_unordered(one, items_for(src), chunksize=2):
            if res is None: continue
            name, n, m, best = res; rows.append((n, m, name, best)); C[len(best) if best is not None else 'none'] += 1
    print('rotation-class instances by least number of rotations on a successful run:', dict(C))
    for n, m, name, best in sorted(rows): print('  %s n=%d m=%d rotated cycle lengths %s' % (name, n, m, best))
