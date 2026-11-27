"""Open fact (A) of k4/vm.md section 7.5: for instances where some V-M matching extends, count, over every V-M matching
Y and every EFX0 extension X of Y (brute force over the placements of the pool), how many extensions have an acyclic
precedence digraph (k -> j iff theta_k(X_j) > v_k(Y_k)).  Reports the smallest instances where some extension is
cyclic (so (A) needs a choice of extension), and any where every extension is cyclic (would refute (A)).
EVIDENCE only.
    python3 k4/vm/vm_prec2.py SOURCE"""
import sys, os, itertools, collections, json, time, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
from vm_test import items_for
from vm_prec import theta, acyclic


def one(args):
    name, sets, vals, m = args
    I = V.Inst(sets, vals, m); tot = acy = 0; witness = None
    for ch, r in V.all_runs(V.vm_run, I, stop='II'):
        if isinstance(r, V.Stuck): continue
        Y = [list(b) for b in r[0]]; pool = [g for g in range(m) if not any(g in b for b in Y)]
        if len(pool) > 7: return name, I.n, I.m, sets, vals, None, None, None
        for own in itertools.product(range(I.n), repeat=len(pool)):
            X = [list(b) for b in Y]
            for g, o in zip(pool, own): X[o].append(g)
            if not V.is_efx0(I, X): continue
            tot += 1
            Ed = {k: [j for j in range(I.n) if j != k and theta(I, k, X[j]) > I.val(k, Y[k])] for k in range(I.n)}
            if acyclic(I.n, Ed): acy += 1
            elif witness is None: witness = (Y, X, {k: v for k, v in Ed.items() if v})
    return name, I.n, I.m, sets, vals, tot, acy, witness


if __name__ == '__main__':
    src = sys.argv[1]; print('$ python3 k4/vm/vm_prec2.py', ' '.join(sys.argv[1:]))
    C = collections.Counter(); mixed = []; allcyc = []; t0 = time.time()
    with mp.Pool(os.cpu_count()) as pool:
        for name, n, m, sets, vals, tot, acy, wit in pool.imap_unordered(one, items_for(src), chunksize=4):
            if tot is None: C['skipped (pool > 7)'] += 1; continue
            if tot == 0: C['no V-M matching extends'] += 1; continue
            C['instances with an extension'] += 1
            if acy == tot: C['every extension acyclic'] += 1
            elif acy > 0: C['some cyclic, some acyclic'] += 1; mixed.append((n, m, sum(map(len, sets)), name, sets, vals, tot, acy, wit))
            else: C['EVERY extension cyclic (refutes A)'] += 1; allcyc.append((n, m, name, sets, vals, tot, wit))
    for k in sorted(C): print('%-40s %d' % (k, C[k]))
    for n, m, s_, name, sets, vals, tot, acy, wit in sorted(mixed)[:4]:
        print('  mixed: %s n=%d m=%d extensions %d acyclic %d %s' % (name, n, m, tot, acy, json.dumps({'sets': sets, 'vals': vals, 'm': m})))
        print('     a cyclic one: Y=%s X=%s precedence=%s' % wit)
    for x in sorted(allcyc)[:4]:
        print('  ALL CYCLIC:', x[2], 'n=%d m=%d' % (x[0], x[1]), json.dumps({'sets': x[3], 'vals': x[4], 'm': x[1]}))
    print('time %.0f s' % (time.time() - t0))
