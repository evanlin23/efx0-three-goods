"""Check the claims in the proof of Theorem VM (k4/vm.md section 8) on every run of the reconstruction (main reading):
  (C1) after Phase III, every agent that values an unassigned good is in S = N1 u N2r u (Phase-I winners);
  (C2) the partial allocation is EFX after Phase II and after each of Phase III's three matchings;
  (C3) at every EFX-graph step the graph is acyclic and its longest directed path has at most 2 edges;
  (C4) the bundles of S-agents are subsets of their R_i at every EFX-graph step.
Independent of vmlib's own run: it re-runs the phases with the same chooser and recomputes the EFX graph.
    python3 k4/vm/vm_thm_check.py SOURCE [--limit=N]"""
import sys, os, collections, time, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
from vm_test import items_for


def longest_path(nodes, edges):
    memo = {}
    def lp(u, stack):
        if u in stack: raise ValueError('cycle')
        if u in memo: return memo[u]
        stack.add(u); best = 0
        for w in edges.get(u, ()):
            best = max(best, 1 + lp(w, stack))
        stack.discard(u); memo[u] = best; return best
    return max((lp(u, set()) for u in nodes), default=0)


def checked_run(I, ch):
    n, m = I.n, I.m
    X = [[] for _ in range(n)]; owner = {}; avail = set(range(m)); log = []
    def strong(i):
        r = I.rank[i]
        if not r: return False
        a = I.v[i][r[0]]; b = I.v[i][r[1]] if len(r) > 1 else 0; c = I.v[i][r[2]] if len(r) > 2 else 0
        return a > b + c
    A = set(i for i in range(n) if strong(i))
    MA = V.matching_step(I, ch, A, avail, 1, 'G', 'I', X, owner, log)
    Nr = set(range(n)) - MA; Nk = {}
    for k in (1, 2, 3, 4):
        Nk[k] = V.matching_step(I, ch, Nr, avail, k, 'G', 'II.%d' % k, X, owner, log); Nr -= Nk[k]
    assert V.is_efx(I, X), 'C2 after II'
    V.matching_step(I, ch, Nk[3], avail, 4, 'G', 'III.3-4', X, owner, log); assert V.is_efx(I, X), 'C2 III.a'
    N2r = V.matching_step(I, ch, Nk[2], avail, 3, 'G', 'III.2-3', X, owner, log); assert V.is_efx(I, X), 'C2 III.b'
    V.matching_step(I, ch, Nk[2] - N2r, avail, 4, 'G', 'III.2-4', X, owner, log); assert V.is_efx(I, X), 'C2 III.c'
    S = set(Nk[1]) | set(N2r) | set(MA)
    assert all(i in S for g in avail for i in I.valued_by(g)), 'C1'
    maxlp = 0
    while True:
        valued = sorted(g for g in avail if I.valued_by(g))
        if not valued: break
        g = ch.pick('egood', valued)
        assert all(set(X[i]) <= set(I.sets[i]) for i in S), 'C4'
        nodes = [i for i in sorted(S) if g in I.v[i]]
        edges = {i: [i2 for i2 in nodes if i2 != i and V.efx_envies(I, X, i, X[i2] + [g])] for i in nodes}
        try:
            lp = longest_path(nodes, edges)
        except ValueError:
            raise AssertionError('C3 cycle')
        assert lp <= 2, 'C3 path %d' % lp
        maxlp = max(maxlp, lp)
        src = [i for i in nodes if not any(i in edges[u] for u in nodes)]
        s = ch.pick(('esrc', g), src)
        X[s].append(g); avail.discard(g)
    assert V.is_efx(I, X), 'final'
    return maxlp


def one(args):
    name, sets, vals, m, limit = args
    I = V.Inst(sets, vals, m); c = collections.Counter()
    for chs, r in V.all_runs(checked_run, I, limit=limit):
        if isinstance(r, V.Stuck): c['stuck'] += 1
        else: c['runs'] += 1; c['lp%d' % r] += 1
    return c


if __name__ == '__main__':
    src = sys.argv[1]; opt = dict(a[2:].split('=') for a in sys.argv[2:] if a.startswith('--'))
    limit = int(opt.get('limit', 500)); t0 = time.time()
    print('$ python3 k4/vm/vm_thm_check.py', ' '.join(sys.argv[1:]))
    C = collections.Counter(); N = 0
    with mp.Pool(os.cpu_count()) as pool:
        for c in pool.imap_unordered(one, [(a, b, cc, d, limit) for a, b, cc, d in items_for(src)], chunksize=8):
            C.update(c); N += 1
    print('instances', N, dict(sorted(C.items())), 'time %.0f s' % (time.time() - t0))
