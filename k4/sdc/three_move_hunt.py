"""Hunt for a start needing three sequential moves (a counterexample to OC2^max, k4/sdc.md §31).  Seeds: the 11 n = 4
OC1^max-failing cores (one exported two-move start each, results/k4_oc1max/two_move_starts_n4.json.gz) and the n = 5
OC1'-failure 5_pure idx 164.  A seed is extended by 1 or 2 new agents, each with 3-4 relevant goods drawn from the seed's
goods (junk preferred, so the new agents value the junk and cannot serve as free sinks) and fresh goods; values random.
The extension is kept if it is a strict connected k = 4 core (oc1max_climb.is_core).  Then every maximum-matching SD
start of the extension is classified by the least number of sequential official moves (k4/sdc.md §29) after which a
one-absorber completion exists (0, 1, 2 or '>=3'); a '>=3' start is printed and must be replayed independently.
Completion test: exhaustive numpy enumeration of junk assignments (at most one agent with >= 2 junk goods), raw EFX0.
    python3 k4/sdc/three_move_hunt.py TRIALS SEED [EXTRA_AGENTS]"""
import sys, os, gzip, json, random, itertools, collections, time, multiprocessing as mp
import numpy as np
import _paths  # noqa: F401
from oc1_mc2_rand import Inst
from oc1_max_orders import nu
import oc1max_climb as C

RES = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'results')
BIG = 10 ** 9


def complete(I, base, absorbers=1):
    n, m = I.n, I.m
    J = [g for g in range(m) if all(g not in b for b in base)]
    if not J: return I.efx0(base)
    Vm = np.zeros((n, m), dtype=np.int64)
    for i in range(n):
        for g, x in I.v[i].items(): Vm[i, g] = x
    A = np.array(list(itertools.product(range(n), repeat=len(J))), dtype=np.int64)
    cnt = np.zeros((len(A), n), dtype=np.int64); rows = np.arange(len(A))
    for k in range(len(J)): np.add.at(cnt, (rows, A[:, k]), 1)
    A = A[(cnt >= 2).sum(1) <= absorbers]; rows = np.arange(len(A))
    W0 = np.array([[Vm[i, base[j]].sum() if base[j] else 0 for j in range(n)] for i in range(n)])
    M0 = np.array([[Vm[i, base[j]].min() if base[j] else BIG for j in range(n)] for i in range(n)])
    W = np.repeat(W0[None], len(A), 0); M = np.repeat(M0[None], len(A), 0)
    NE = np.repeat(np.array([bool(b) for b in base])[None], len(A), 0)
    for k, g in enumerate(J):
        j = A[:, k]
        W[rows, :, j] += Vm[:, g][None, :]
        M[rows, :, j] = np.minimum(M[rows, :, j], Vm[:, g][None, :])
        NE[rows, j] = True
    own = W[:, np.arange(n), np.arange(n)]
    viol = (W - M > own[:, :, None]) & NE[:, None, :]
    viol[:, np.arange(n), np.arange(n)] = False
    return bool((~viol.any(axis=(1, 2))).any())


def depth(I, picks, maxd=2):
    key = lambda s: tuple(tuple(sorted(b)) for b in s)
    base = [[g] if g is not None else [] for g in picks]
    level = {key(base)}; seen = set(level)
    for d in range(maxd + 1):
        for s in level:
            if complete(I, [list(b) for b in s]): return d
        if d == maxd: return '>=%d' % (maxd + 1)
        nxt = set()
        for s in level:
            for t in I.moves([list(b) for b in s]):
                if t not in seen: seen.add(t); nxt.add(t)
        level = nxt


def seeds():
    out = []
    d = json.load(gzip.open(os.path.join(RES, 'k4_oc1max', 'two_move_starts_n4.json.gz')))
    for h in d['hypergraphs']: out.append((h['sets'], h['starts'][0]['vals']))
    out.append(([[0, 2, 3, 7], [1, 2, 6, 7], [3, 4, 5, 6], [3, 4, 5, 7], [4, 5, 6, 7]],
                [[1, 8, 6, 4], [4, 8, 2, 7], [6, 7, 3, 5], [7, 10, 2, 6], [7, 5, 3, 6]]))
    return out


def strict_vals(d, rng):
    while True:
        x = [rng.randint(1, 30) for _ in range(d)]
        if 2 * max(x) >= sum(x): continue
        sums = collections.defaultdict(list); ok = True
        for r in range(1, d + 1):
            for T in itertools.combinations(range(d), r): sums[sum(x[k] for k in T)].append(set(T))
        for L in sums.values():
            if any(not (a & b) for a, b in itertools.combinations(L, 2)): ok = False; break
        if ok: return x


def trial(args):
    seed, extra = args
    rng = random.Random(seed); S = seeds()
    sets, vals = S[rng.randrange(len(S))]
    sets = [list(s) for s in sets]; vals = [list(v) for v in vals]
    I0 = Inst(sets, vals); m0 = I0.m
    for _ in range(extra):
        m = 1 + max(max(s) for s in sets)
        d = rng.choice([3, 4]); pool = list(range(m)) + [m, m + 1]
        s = sorted(rng.sample(pool, d))
        ren = {}; nxt = m
        for g in s:
            if g >= m: ren[g] = nxt; nxt += 1
        s = [ren.get(g, g) for g in s]
        sets.append(s); vals.append(strict_vals(d, rng))
    if not C.is_core(sets, vals, False): return seed, None
    I = Inst(sets, vals); N = nu(I); out = collections.Counter(); bad = []
    pv = {I.sd(o) for o in itertools.permutations(range(I.n))}
    for p in pv:
        if sum(x is not None for x in p) != N: continue
        r = depth(I, p); out[r] += 1
        if r == '>=3': bad.append(p)
    return seed, (sets, vals, dict(out), bad)


if __name__ == '__main__':
    T, SEED = int(sys.argv[1]), int(sys.argv[2]); EXTRA = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    print('$ python3 k4/sdc/three_move_hunt.py', *sys.argv[1:], flush=True)
    t0 = time.time(); TOT = collections.Counter()
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for seed, r in pool.imap_unordered(trial, [(SEED * 100003 + t, EXTRA) for t in range(T)]):
            if r is None: TOT['not a core'] += 1; continue
            sets, vals, out, bad = r; TOT['cores'] += 1
            for k, c in out.items(): TOT['starts needing %s moves' % k] += c
            if bad: print('THREE-MOVE CANDIDATE', json.dumps({'sets': sets, 'vals': vals, 'picks': bad}), flush=True)
            if TOT['cores'] % 50 == 0: print('...', dict(TOT), '%.0f s' % (time.time() - t0), flush=True)
    for k in sorted(TOT): print(k, TOT[k])
    print('time %.0f s' % (time.time() - t0))
