"""Lemma EXT's hypothesis on the data (k4/vm.md section 7.5).  For a V-M matching Y and an EFX0 allocation X that
extends Y (picks kept), let k -> j ("k must be completed before j's bundle is") when theta_k(X_j) > v_k(Y_k), where
theta_k(B) = v_k(B) - min_{h in B} v_k(h).  Lemma EXT: if this digraph is acyclic, F1 placements without rotation
reach X (fill the bundles in a topological order).  For every instance in the classes 'absorbers' and 'unfreezing'
of vm_classify.py: does some V-M matching have an extension with an acyclic precedence digraph?  Brute force over
the placements of the pool.  EVIDENCE only.
    python3 k4/vm/vm_prec.py SOURCE"""
import sys, os, itertools, collections, time, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
from vm_test import items_for
from vm_extend import Enc
from vm_classify import classify, ORDER


def theta(I, k, B):
    if len(B) < 2: return 0
    return I.val(k, B) - min(I.v[k].get(h, 0) for h in B)


def acyclic(n, E):
    color = [0] * n
    def dfs(u):
        color[u] = 1
        for w in E[u]:
            if color[w] == 1 or (color[w] == 0 and not dfs(w)): return False
        color[u] = 2; return True
    return all(color[u] or dfs(u) for u in range(n))


def one(args):
    name, sets, vals, m = args
    I = V.Inst(sets, vals, m); E = Enc(sets, vals, m)
    c = classify(I, E)
    if ORDER[c] not in ('absorbers', 'unfreezing', 'HDT'):
        return name, I.n, I.m, ORDER[c], None, 0
    found = False; nexts = 0
    for ch, r in V.all_runs(V.vm_run, I, stop='II'):
        if isinstance(r, V.Stuck): continue
        Y = [list(b) for b in r[0]]; pool = [g for g in range(m) if not any(g in b for b in Y)]
        if len(pool) > 8: continue
        for own in itertools.product(range(I.n), repeat=len(pool)):
            X = [list(b) for b in Y]
            for g, o in zip(pool, own): X[o].append(g)
            if not V.is_efx0(I, X): continue
            nexts += 1
            Ed = {k: [j for j in range(I.n) if j != k and theta(I, k, X[j]) > I.val(k, Y[k])] for k in range(I.n)}
            if acyclic(I.n, Ed): found = True; break
        if found: break
    return name, I.n, I.m, ORDER[c], found, nexts


if __name__ == '__main__':
    src = sys.argv[1]; print('$ python3 k4/vm/vm_prec.py', ' '.join(sys.argv[1:]))
    C = collections.Counter(); bad = []; t0 = time.time()
    with mp.Pool(os.cpu_count()) as pool:
        for name, n, m, cl, found, ne in pool.imap_unordered(one, items_for(src), chunksize=4):
            if found is None: continue
            C[(cl, 'acyclic extension' if found else 'every extension cyclic')] += 1
            if not found: bad.append((n, m, name, cl))
    for k in sorted(C): print('  %-50s %d' % (' / '.join(k), C[k]))
    for n, m, name, cl in sorted(bad)[:10]: print('  cyclic only:', name, 'n=%d m=%d' % (n, m), cl)
    print('time %.0f s' % (time.time() - t0))
