"""Where value domination stops (k4/sdc.md §28).  P1 (K4.SDC.P1) is refuted by a partial EFX0 allocation with two
two-good bundles that no complete EFX0 allocation value-dominates (GM4-E).  Here: every partial EFX0 allocation whose
bundles are subsets of the holders' relevant goods, with at most one bundle of two goods and the others of at most one
good ('one pair'), is tested for value domination by a complete EFX0 allocation (only the Pareto-maximal value vectors
of such allocations need testing).  Also the same with two pairs, to compare with P1.

    python3 k4/sdc/pdom.py screen|suite|special|cores:FILES N SEED [PAIRS]"""
import sys, os, json, gzip, random, itertools, collections, time
import _paths
from sdclib import Enc
from sdc_need import instances
from nof_var import SPECIAL
from pysat.solvers import Cadical153


def dominated_vec(E, u):
    cl = list(E.cl)
    for g in range(E.m): cl.append([-E.x[g][E.n]])
    for i in range(E.n):
        for S, y in E.y[i].items():
            if E.val(i, S) < u[i]: cl.append([-y])
    S = Cadical153(bootstrap_with=cl); ok = S.solve(); S.delete(); return ok


def efx0_partial(E, B):
    for i in range(E.n):
        vi = E.val(i, B[i])
        for j in range(E.n):
            if j == i or not B[j]: continue
            for h in B[j]:
                if E.val(i, [g for g in B[j] if g != h]) > vi: return False
    return True


def allocations(E, pairs):
    """partial allocations: each agent a subset of R_i of size <= 1, at most `pairs` agents of size 2, disjoint"""
    out = []
    def rec(i, used, B, p):
        if i == E.n: out.append(list(B)); return
        rec(i + 1, used, B + [()], p)
        for g in E.R[i]:
            if g not in used: rec(i + 1, used | {g}, B + [(g,)], p)
        if p < pairs:
            for S in itertools.combinations(E.R[i], 2):
                if not (set(S) & used): rec(i + 1, used | set(S), B + [S], p + 1)
    rec(0, frozenset(), [], 0)
    return out


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    PAIRS = int(sys.argv[-1]) if sys.argv[-1] in ('1', '2', '3') else 1
    print('$ python3 k4/sdc/pdom.py', *sys.argv[1:], flush=True)
    if src == 'special': items = SPECIAL
    elif src.startswith('cores:'):
        N, seed = int(sys.argv[2]), int(sys.argv[3]); rng = random.Random(seed); items = []
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        from de4lib import random_profile
        os.chdir(cwd)
        cores = []
        for fn in src[6:].split(','):
            cores += [c['sets'] for c in json.load(gzip.open(os.path.join(_paths.ROOT, 'results', fn)))['cores']]
        for t in range(N):
            sets = rng.choice(cores); items.append(('r%d' % t, sets, random_profile(sets, rng), 1 + max(max(x) for x in sets)))
    else:
        items = instances(src)
    for name, sets, vals, m in items:
        if len(sets) > 5: continue
        E = Enc(sets, vals, m); C['instances'] += 1
        vecs = {}
        for B in allocations(E, PAIRS):
            u = tuple(E.val(i, B[i]) for i in range(E.n))
            if u in vecs: continue
            if efx0_partial(E, B): vecs[u] = B
        top = [u for u in vecs if not any(w != u and all(a >= b for a, b in zip(w, u)) for w in vecs)]
        bad = [u for u in top if not dominated_vec(E, u)]
        C['Pareto-maximal value vectors tested'] += len(top); C['not dominated'] += len(bad)
        C['instances with one not dominated'] += bool(bad)
        if bad and C['shown'] < 4:
            C['shown'] += 1; print('NOT DOMINATED', name, json.dumps((sets, vals)), 'allocation', vecs[bad[0]], 'values', bad[0], flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
