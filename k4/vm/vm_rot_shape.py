"""Shape of the single rotation in the rotation class (k4/vm.md section 7.6): for a successful one-rotation run,
the rotated cycle c_0 -> c_1 -> ... (c_t envies c_{t+1}'s bundle and takes it).  For each arrow: is it a WANT arrow
(the bundle taken is the holder's single pick, which c_t prefers to its own pick) or a PAIR arrow (the bundle taken is
a pick plus pool goods, and c_t values that set above its own bundle), and how many pool goods ride along.
EVIDENCE only.
    python3 k4/vm/vm_rot_shape.py SOURCE"""
import sys, os, collections, time, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
from vm_test import items_for
from vm_extend import Enc
from vm_classify import classify, ORDER


def one(args):
    name, sets, vals, m = args
    I = V.Inst(sets, vals, m); E = Enc(sets, vals, m)
    if ORDER[classify(I, E)] != 'rotation': return None
    for ch, r in V.all_runs(V.vm_run, I, stop='II'):
        if isinstance(r, V.Stuck): continue
        Y = [list(b) for b in r[0]]
        stack = [([list(b) for b in Y], None)]
        while stack:
            X, rot = stack.pop()
            Ecyc = V.find_cycle(V.envy_graph(I, X), I.n)
            if Ecyc is not None:
                if rot is not None: continue                     # a second rotation: skip (we want one-rotation runs)
                arrows = []
                for t, c in enumerate(Ecyc):
                    d = Ecyc[(t + 1) % len(Ecyc)]; B = X[d]; extra = [g for g in B if g not in Y[d]]
                    kind = 'want' if not extra else 'pair'
                    arrows.append((c, d, kind, len(extra), sum(1 for g in extra if g in I.v[c])))
                Z = [list(b) for b in X]
                B = [list(X[c]) for c in Ecyc]
                for t, c in enumerate(Ecyc): Z[c] = B[(t + 1) % len(Ecyc)]
                X, rot = Z, arrows
            pool = set(range(m)) - set(g for b in X for g in b); valued = sorted(g for g in pool if I.valued_by(g))
            if not valued:
                if rot is not None: return name, I.n, I.m, rot
                continue
            for g in valued:
                for s in range(I.n):
                    if V.safe_add(I, X, s, g):
                        Z = [list(b) for b in X]; Z[s].append(g); stack.append((Z, rot))
    return name, I.n, I.m, None


if __name__ == '__main__':
    src = sys.argv[1]; print('$ python3 k4/vm/vm_rot_shape.py', ' '.join(sys.argv[1:]))
    C = collections.Counter()
    with mp.Pool(os.cpu_count()) as pool:
        for res in pool.imap_unordered(one, items_for(src), chunksize=2):
            if res is None: continue
            name, n, m, arrows = res
            print('  %s n=%d m=%d arrows (taker, holder, kind, pool goods in the bundle taken, of which the taker values): %s' % (name, n, m, arrows))
            if arrows:
                C[tuple(sorted((a[2], a[3]) for a in arrows))] += 1
    print('cycle shapes (kind, pool goods):', dict(C))
