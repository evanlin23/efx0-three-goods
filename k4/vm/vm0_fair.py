"""F4 by a canonical choice of SD outcome (k4/vm.md section 7).  Each SD outcome Y has a rank vector (rank of Y_i in
i's ranking, 5 for no good).  Selection rules over all SD outcomes:
  fair   lexicographically fewest agents with no good, then rank 4, then rank 3, then rank 2 (leximin on ranks)
  rmax   lexicographically most agents with rank 1, then 2, then 3, then 4 (rank-maximal; V-M's greedy is one)
  vm     V-M's own matchings (Phases I-II, every resolution)
For each rule: does every / some selected outcome extend to an EFX0 allocation (SAT), and does the repair
(vmlib.vm0_run with F2, rotation, F1, F3) end EFX0 from every / some selected outcome (some resolution of its
choices)?  EVIDENCE only.
    python3 k4/vm/vm0_fair.py SOURCE [--limit=N] [--maxorders=N]"""
import sys, os, json, itertools, collections, random, time, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
from vm_test import items_for
from vm_extend import completable, Enc
from vm0_sd import sd, some_run


def rankvec(I, Y):
    return [I.rank[i].index(g) + 1 if g is not None else 5 for i, g in enumerate(Y)]


def key_fair(r):
    return tuple(r.count(k) for k in (5, 4, 3, 2))


def key_rmax(r):
    return tuple(-r.count(k) for k in (1, 2, 3, 4))


def one(args):
    name, sets, vals, m, limit, maxorders = args
    I = V.Inst(sets, vals, m); E = Enc(sets, vals, m)
    rng = random.Random(1)
    orders = itertools.permutations(range(I.n)) if I.n <= 7 else (rng.sample(range(I.n), I.n) for _ in range(maxorders))
    outs = set(tuple(sd(I, o)) for o in orders)
    vmY = set()
    for ch, res in V.all_runs(V.vm_run, I, limit=3000, stop='II'):
        if not isinstance(res, V.Stuck):
            X = res[0]; vmY.add(tuple(X[i][0] if X[i] else None for i in range(I.n)))
    sel = {}
    for rule, key in (('fair', key_fair), ('rmax', key_rmax)):
        best = min(key(rankvec(I, Y)) for Y in outs)
        sel[rule] = [Y for Y in outs if key(rankvec(I, Y)) == best]
    sel['vm'] = sorted(vmY, key=str)
    res = {}
    cache = {}
    for rule, L in sel.items():
        e = []; r = []
        for Y in L:
            if Y not in cache:
                cache[Y] = (completable(E, [[g] if g is not None else [] for g in Y]), some_run(I, list(Y), limit, True)[0])
            e.append(cache[Y][0]); r.append(cache[Y][1])
        res[rule] = (len(L), sum(e), sum(r))
    return name, I.n, I.m, res


def main():
    src = sys.argv[1]
    opt = dict(a[2:].split('=') for a in sys.argv[2:] if a.startswith('--'))
    limit = int(opt.get('limit', 1000)); maxorders = int(opt.get('maxorders', 300))
    print('$ python3 k4/vm/vm0_fair.py', ' '.join(sys.argv[1:]))
    t0 = time.time(); C = collections.Counter(); bad = collections.defaultdict(list)
    with mp.Pool(os.cpu_count()) as pool:
        for name, n, m, res in pool.imap_unordered(one, [(a, b, c, d, limit, maxorders) for a, b, c, d in items_for(src)], chunksize=2):
            C['instances'] += 1
            for rule, (k, e, r) in res.items():
                C[rule + ': every selected extends'] += e == k
                C[rule + ': some selected extends'] += e > 0
                C[rule + ': repair from every selected'] += r == k
                C[rule + ': repair from some selected'] += r > 0
                if r == 0: bad[rule].append((n, m, name))
    for k in sorted(C): print('%-45s %d' % (k, C[k]))
    for rule, L in bad.items():
        print('  %s: no selected outcome repairs (%d):' % (rule, len(L)), ', '.join('%s(n=%d,m=%d)' % (nm, n, m) for n, m, nm in sorted(L)[:10]))
    print('time %.0f s' % (time.time() - t0))


if __name__ == '__main__':
    main()
