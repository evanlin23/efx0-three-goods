"""Which canonical MD EFX0 allocation is SIMPLE with one absorber (kgen/rounds.md §4.11)?  For every perfect start,
among its MD EFX0 allocations, the maximisers of several potentials are tested for SIMPLE (every pick-graph component
fixed, ring, rho or rho-fix) and one absorber (Theorem ROUND-SIMPLE's outside count).  A potential whose maximiser is
always simple would be the target of a minimal-counterexample proof of SIMPLE-MD.
Potentials (maximised; ties: every maximiser must be simple for 'all', some for 'some'):
  keepers   number of agents holding their own pick
  picks     number of agents holding exactly one pick (their own or a received one)
  util      sum of v_i(X_i) / v_i(all goods)
  nash      product of v_i(X_i) / p_i
  minrat    min_i v_i(X_i) / p_i (leximin of the ratios)
  junk      minus the number of agents holding two or more non-pick goods (absorbers)
  and lexicographic combinations (picks,junk), (junk,picks), (picks,junk,util), (picks,-keepers), ...
    TARGET=witness: test whether the maximisers are witnesses of a round of OC1' moves instead
    python3 kgen/rounds/simple_potential.py KIND FILE [STRIDE] [JOBS]"""
import sys, os, json, math, collections, time, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import rndlib, recs_vs_rndp as RV
from splice_search import rows_of, dense
TARGET = os.environ.get('TARGET', 'simple')   # simple (SIMPLE + one absorber) or witness (a round of OC1' moves)
from rndp_structure import shapes, outside_one_absorber


def job(row):
    V = dense(row['sets'], row['vals']); n, m = len(V), len(V[0]); y = tuple(row['picks']); picks = set(y)
    tot = [sum(r) for r in V]; p = [V[a][y[a]] for a in range(n)]
    alls, _ = rndlib.list_efx(V); md = []
    for o in alls:
        X = [[g for g in range(m) if o[g] == i] for i in range(n)]
        val = [sum(V[a][g] for g in X[a]) for a in range(n)]
        if any(val[a] < p[a] for a in range(n)): continue
        f = [o[y[a]] for a in range(n)]
        good = all(s in ('fixed', 'ring', 'rho', 'rho-fix') for s in shapes(f, n)) and outside_one_absorber(V, y, X, f)
        if TARGET == 'witness': good = bool(RV.structures(V, y, X, False))
        npk = [sum(1 for g in X[a] if g in picks) for a in range(n)]
        pot = {'keepers': sum(1 for a in range(n) if f[a] == a), 'picks': sum(1 for a in range(n) if npk[a] == 1),
               'util': round(sum(val[a] / tot[a] for a in range(n)), 12),
               'nash': round(sum(math.log(val[a] / p[a]) for a in range(n)), 12),
               'minrat': tuple(sorted(round(val[a] / p[a], 12) for a in range(n))),
               'junk': -sum(1 for a in range(n) if sum(1 for g in X[a] if g not in picks) >= 2)}
        pot['picks,junk'] = (pot['picks'], pot['junk']); pot['junk,picks'] = (pot['junk'], pot['picks'])
        pot['picks,junk,util'] = (pot['picks'], pot['junk'], pot['util'])
        pot['picks,-keepers'] = (pot['picks'], -pot['keepers']); pot['picks,junk,-keepers'] = (pot['picks'], pot['junk'], -pot['keepers'])
        pot['picks,minrat'] = (pot['picks'], pot['minrat']); pot['picks,junk,minrat'] = (pot['picks'], pot['junk'], pot['minrat'])
        md.append((good, pot))
    res = {}
    if not md: return row, None
    for k in md[0][1]:
        best = max(t[1][k] for t in md); arg = [t[0] for t in md if t[1][k] == best]
        res[k] = ('all' if all(arg) else 'some' if any(arg) else 'none')
    res['any simple'] = any(t[0] for t in md); res['all simple'] = all(t[0] for t in md)
    return row, res


if __name__ == '__main__':
    kind, fn = sys.argv[1], sys.argv[2]; STRIDE = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    JOBS = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    print('$ python3 kgen/rounds/simple_potential.py', *sys.argv[1:], flush=True)
    rows = rows_of(kind, fn, STRIDE); C = collections.Counter(); bad = collections.defaultdict(list); t0 = time.time()
    with mp.Pool(JOBS) as pool:
        for row, res in pool.imap_unordered(job, rows, chunksize=8):
            if res is None: C['starts without an MD allocation'] += 1; continue
            C['starts'] += 1
            if res['all simple']: C['starts where every MD allocation is good (%s)' % TARGET] += 1; continue
            C['starts with an MD allocation that is not good (%s)' % TARGET] += 1
            for k, v in res.items():
                if k in ('any simple', 'all simple'): continue
                C[(k, 'maximisers simple: ' + v)] += 1
                if v != 'all' and len(bad[k]) < 2: bad[k].append({x: row[x] for x in ('list', 'idx', 'sets', 'vals', 'picks')})
    for k in sorted(C, key=str): print(k, C[k])
    for k, v in bad.items():
        for e in v: print('A MAXIMISER IS NOT GOOD', k, json.dumps(e))
    print('time %.0f s' % (time.time() - t0))
