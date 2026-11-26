"""Fast check of Conjecture VM1 (k4/vm.md section 7.3) with early exit: for each V-M matching Y, first Y itself,
then every state one move away (pool upgrade or unrestricted two-agent exchange); stop at the first state from which
F1 placements with rotation complete (DFS with early exit, capped).  Reports per instance the fewest moves found
(0, 1) or FAIL (within the caps; a FAIL is then re-checked with larger caps).  Every completed allocation is
re-checked with the raw EFX0 definition.  EVIDENCE only.
    python3 k4/vm/vm1_fast.py SOURCE [--bcap=N]"""
import sys, os, collections, json, time, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
import vmx2_phases as P
from vm_test import items_for


def complete(I, X0, pool0, cap):
    """DFS over F1 placements with rotation; returns a complete EFX0 allocation or None"""
    stack = [([list(b) for b in X0], set(pool0))]; leaves = 0
    while stack and leaves < cap:
        X, pool = stack.pop(); V.l3_source(I, X)
        valued = sorted(g for g in pool if I.valued_by(g))
        if not valued:
            J = sorted(pool)
            if J:
                s = V.l3_source(I, X); X[s] += J
            return X
        br = False
        for g in valued:
            for s in range(I.n):
                if V.safe_add(I, X, s, g):
                    Y = [list(b) for b in X]; Y[s].append(g); stack.append((Y, pool - {g})); br = True
        if not br: leaves += 1
    return None


def vm1(I, cap):
    V.FREE_Z[0] = True
    Ys = []
    for ch, r in V.all_runs(V.vm_run, I, stop='II'):
        if not isinstance(r, V.Stuck):
            Y = [list(b) for b in r[0]]
            if Y not in Ys: Ys.append(Y)
    for depth in (0, 1):
        for Y in Ys:
            pool = set(range(I.m)) - set(g for b in Y for g in b)
            Z0 = [list(b) for b in Y]; V.l3_source(I, Z0)
            cands = [(Z0, pool)] if depth == 0 else [P.apply_move(Z0, pool, mv) for mv in V.exchanges(I, Z0, pool)]
            for Z, Pz in cands:
                X = complete(I, Z, Pz, cap)
                if X is not None:
                    assert V.is_efx0(I, X)
                    return depth
    return None


def one(args):
    name, sets, vals, m, cap = args
    I = V.Inst(sets, vals, m); t = time.time(); d = vm1(I, cap)
    if d is None:
        d2 = vm1(I, 50 * cap)
        return name, I.n, I.m, max(map(len, sets)), d2, True, time.time() - t, sets, vals
    return name, I.n, I.m, max(map(len, sets)), d, False, time.time() - t, sets, vals


if __name__ == '__main__':
    src = sys.argv[1]; opt = dict(a[2:].split('=') for a in sys.argv[2:] if a.startswith('--')); cap = int(opt.get('bcap', 2000))
    print('$ python3 k4/vm/vm1_fast.py', ' '.join(sys.argv[1:]))
    C = collections.Counter(); fails = []; tmax = 0; t0 = time.time()
    with mp.Pool(os.cpu_count()) as pool:
        for name, n, m, k, d, rechecked, dt, sets, vals in pool.imap_unordered(one, [(a, b, c, dd, cap) for a, b, c, dd in items_for(src)], chunksize=1):
            C['instances'] += 1; C['fewest moves %s' % d] += 1; tmax = max(tmax, dt)
            if rechecked: C['needed the larger cap'] += 1
            if d is None: fails.append((n, m, name, sets, vals))
    for k in sorted(C): print('%-30s %d' % (k, C[k]))
    for n, m, name, sets, vals in sorted(fails)[:5]:
        print('  FAIL %s n=%d m=%d %s' % (name, n, m, json.dumps({'sets': sets, 'vals': vals, 'm': m})))
    print('slowest %.1f s; time %.0f s' % (tmax, time.time() - t0))
