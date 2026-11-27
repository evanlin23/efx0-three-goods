"""V-M matchings versus maximum matchings (coordinator's question, k4/vm.md section 7.4).  For every instance and
every V-M matching Y (Phases I-II, every resolution): |Y| versus nu (maximum matching of the agent / relevant-good
graph); whether the no-move completion (F1 placements with rotation from Y, DFS capped) succeeds; and for a successful
no-move run, whether its output still contains Y (picks kept as bases) and is one-absorber (at most one agent got two
or more further goods), i.e. has the shape of OC1's completion.  EVIDENCE only.
    python3 k4/vm/vm_max.py SOURCE [--bcap=N]"""
import sys, os, collections, json, time, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
from vm_test import items_for


def nu(I):
    match = {}
    def aug(i, seen):
        for g in I.sets[i]:
            if g in seen: continue
            seen.add(g)
            if g not in match or aug(match[g], seen):
                match[g] = i; return True
        return False
    return sum(aug(i, set()) for i in range(I.n))


def no_move_runs(I, Y, cap):
    """DFS over F1 placements with rotation from the matching Y; yields final allocations (successes) and counts"""
    m = I.m; out = []; runs = 0
    stack = [[list(b) for b in Y]]
    while stack and runs < cap:
        X = stack.pop(); V.l3_source(I, X)
        pool = set(range(m)) - set(g for b in X for g in b)
        valued = sorted(g for g in pool if I.valued_by(g))
        if not valued:
            runs += 1; out.append(X); continue
        br = False
        for g in valued:
            for s in range(I.n):
                if V.safe_add(I, X, s, g):
                    Z = [list(b) for b in X]; Z[s].append(g); stack.append(Z); br = True
        if not br:
            runs += 1
    return out, runs


def one(args):
    name, sets, vals, m, bcap = args
    I = V.Inst(sets, vals, m); N = nu(I); res = []
    seen = set()
    for ch, r in V.all_runs(V.vm_run, I, stop='II'):
        if isinstance(r, V.Stuck): continue
        Y = [list(b) for b in r[0]]; k = tuple(map(tuple, Y))
        if k in seen: continue
        seen.add(k)
        size = sum(1 for b in Y if b)
        succ, runs = no_move_runs(I, Y, bcap)
        keep = [X for X in succ if all(set(Y[i]) <= set(X[i]) for i in range(I.n))]
        onea = [X for X in keep if sum(1 for i in range(I.n) if len(X[i]) - len(Y[i]) >= 2) <= 1]
        res.append((size == N, bool(succ), bool(keep), bool(onea)))
    return name, I.n, I.m, N, res


if __name__ == '__main__':
    src = sys.argv[1]; opt = dict(a[2:].split('=') for a in sys.argv[2:] if a.startswith('--')); bcap = int(opt.get('bcap', 3000))
    print('$ python3 k4/vm/vm_max.py', ' '.join(sys.argv[1:]))
    C = collections.Counter(); X = collections.Counter(); ex = []; t0 = time.time()
    with mp.Pool(os.cpu_count()) as pool:
        for name, n, m, N, res in pool.imap_unordered(one, [(a, b, c, d, bcap) for a, b, c, d in items_for(src)], chunksize=4):
            C['instances'] += 1; C['V-M matchings'] += len(res)
            C['V-M matchings that are maximum'] += sum(r[0] for r in res)
            C['instances: every V-M matching maximum'] += all(r[0] for r in res)
            C['instances: some V-M matching maximum'] += any(r[0] for r in res)
            for r in res:
                X[('maximum' if r[0] else 'not maximum', 'no-move completes' if r[1] else 'no-move fails')] += 1
                if r[1]:
                    X[('no-move success', 'keeps picks' if r[2] else 'picks moved by rotation', 'one-absorber' if r[3] else '')] += 1
            if not all(r[0] for r in res): ex.append((n, m, name, N, [r[0] for r in res]))
    for k in sorted(C): print('%-45s %d' % (k, C[k]))
    for k in sorted(X): print('  %-75s %d' % (' / '.join(x for x in k if x), X[k]))
    for n, m, name, N, r in sorted(ex)[:6]:
        print('  non-maximum V-M matching: %s n=%d m=%d nu=%d maximum-flags=%s' % (name, n, m, N, r))
    print('time %.0f s' % (time.time() - t0))
