"""Shared helpers for the goods-first / envy-graph exploration (branch proof/k3-simplify). Evidence only.

An algorithm is a function alg(n, m, v) -> X with X[g] = the agent receiving good g (every good allocated), v[i] =
{good: positive value}. Tests use ranking profiles with values (4, 3, 2) (strictly balanced; EFX0 is then ordinal,
Lemma L5) and, at the end, random general instances (ties, top-heavy agents, 0-3 goods per agent).

Suites (the protocol of the task):
  small : every ranking profile from test_k3s.gen_small for (n, m) in (2, 3..6), (3, 4..7), (4, 5..6)
  core5 : lbx.core_profiles(5, sample=200, minn=5)   (61,400 profiles)
  rand  : random ranking profiles n <= 8 and random general instances n <= 8
Single process only.
"""
import sys, os, random, itertools, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..'))
from k3s import efx0, k3s          # noqa: E402
from test_k3s import gen_small     # noqa: E402
from lbx import core_profiles      # noqa: E402

VAL = (4, 3, 2)

def vals(rank, real=VAL):
    return [dict(zip(r, real)) for r in rank]

def ranking(v):
    return [sorted(vi, key=lambda g: (-vi[g], g)) for vi in v]

def bval(vi, B):
    return sum(vi.get(g, 0) for g in B)

def threat(vi, B):
    """theta_i(B): the most i can value B minus one good (0 for a singleton or empty bundle)"""
    if len(B) <= 1: return 0
    s = 0; mn = None
    for g in B:
        x = vi.get(g, 0); s += x
        if mn is None or x < mn: mn = x
    return s - mn

def safe_with(n, v, B, i, j, newB):
    """would agent i (holding B[i]) be safe toward bundle newB placed at j?  (i != j)"""
    return bval(v[i], B[i]) >= threat(v[i], newB)

def all_safe(n, v, B):
    for i in range(n):
        own = bval(v[i], B[i])
        for j in range(n):
            if i != j and threat(v[i], B[j]) > own: return False
    return True

def unsafe_list(n, v, B):
    out = []
    for i in range(n):
        own = bval(v[i], B[i])
        for j in range(n):
            if i != j and threat(v[i], B[j]) > own: out.append((i, j))
    return out

def envy(n, v, B):
    vb = [[bval(v[i], B[j]) for j in range(n)] for i in range(n)]
    return [[j for j in range(n) if j != i and vb[i][j] > vb[i][i]] for i in range(n)]

def find_cycle(n, E):
    color = [0] * n; par = [-1] * n
    for s in range(n):
        if color[s]: continue
        stack = [(s, iter(E[s]))]; color[s] = 1
        while stack:
            u, it = stack[-1]
            w = next(it, None)
            if w is None:
                color[u] = 2; stack.pop(); continue
            if color[w] == 0:
                color[w] = 1; par[w] = u; stack.append((w, iter(E[w])))
            elif color[w] == 1:
                cyc = [u]
                while cyc[-1] != w: cyc.append(par[cyc[-1]])
                return cyc[::-1]        # w -> ... -> u -> w, each envies the next
    return None

def eliminate_cycles(n, v, B):
    """rotate envy cycles (F2) until the envy graph is acyclic; each agent on a cycle takes the next one's bundle"""
    while True:
        E = envy(n, v, B); cyc = find_cycle(n, E)
        if cyc is None: return E
        nb = [B[cyc[(t + 1) % len(cyc)]] for t in range(len(cyc))]
        for t, i in enumerate(cyc): B[i] = nb[t]

def sources(n, E):
    indeg = [0] * n
    for i in range(n):
        for j in E[i]: indeg[j] += 1
    return [i for i in range(n) if indeg[i] == 0]

def to_X(m, B):
    X = [None] * m
    for i, b in enumerate(B):
        for g in b: X[g] = i
    return X

# --------------------------------------------------------------------------------------------- explanation
def explain(n, m, rank, X, real=VAL):
    """one line per unsafe agent: who, its ranking, its bundle, and the bundle it strongly envies"""
    v = vals(rank, real); B = [sorted(g for g in range(m) if X[g] == i) for i in range(n)]
    lines = [f"allocation {B}"]
    for i, j in unsafe_list(n, v, B):
        lines.append(f"agent {i} (ranks {rank[i]}) holds {B[i]} worth {bval(v[i], B[i])}; bundle {B[j]} of agent {j} "
                     f"minus its least good is worth {threat(v[i], B[j])} to it")
    return lines

# --------------------------------------------------------------------------------------------- suites
SMALL = [(2, 3), (2, 4), (2, 5), (2, 6), (3, 4), (3, 5), (3, 6), (3, 7), (4, 5), (4, 6)]

def check_rank(alg, n, m, rank, real=VAL):
    v = vals(rank, real)
    X = alg(n, m, v)
    return X is not None and None not in X and efx0(n, m, v, X), X

def run_small(alg, sets=SMALL, stop=None, log=print, maxfail_set=None):
    """returns dict (n, m) -> (profiles, failures), and the first (smallest) failure"""
    res = {}; first = None
    for (n, m) in sets:
        tot = bad = 0; t = time.time()
        for _, _, rank in gen_small(n, m):
            tot += 1
            ok, X = check_rank(alg, n, m, rank)
            if not ok:
                bad += 1
                if first is None: first = (n, m, rank, X)
                if maxfail_set and bad >= maxfail_set: break
        res[(n, m)] = (tot, bad, bad >= (maxfail_set or 10**18))
        log(f"  small n={n} m={m}: {tot} profiles{' (stopped early)' if res[(n, m)][2] else ''}, failures {bad}  [{time.time() - t:.0f}s]")
        if stop and first is not None and stop(res): break
    return res, first

def run_core5(alg, sample=200, log=print, maxfail=None):
    tot = bad = 0; first = None; t = time.time()
    for n, m, rank in core_profiles(5, sample=sample, minn=5):
        tot += 1
        for real in ((4, 3, 2), (10, 9, 2), (10, 6, 5)):
            ok, X = check_rank(alg, n, m, rank, real)
            if not ok:
                bad += 1
                if first is None or (m, rank) < (first[1], first[2]): first = (n, m, rank, X, real)
                break
        if maxfail and bad >= maxfail: break
    log(f"  core n=5 sample ({sample}/core): {tot} profiles x 3 realizations, failing profiles {bad}  [{time.time() - t:.0f}s]")
    return tot, bad, first

def rand_general(rng, maxn=8):
    n = rng.randint(2, maxn); m = rng.randint(1, 2 * n + 4); v = []
    for i in range(n):
        k = rng.randint(0, min(3, m)) if rng.random() < 0.3 else min(3, m)
        v.append({g: rng.randint(1, 6) for g in rng.sample(range(m), k)})
    return n, m, v

def run_random(alg, K=20000, seed=7, maxn=8, log=print):
    rng = random.Random(seed); badp = badg = 0; firstp = firstg = None; t = time.time()
    for _ in range(K):
        n = rng.randint(2, maxn); m = rng.randint(max(3, n), 2 * n + 3)
        rank = [tuple(rng.sample(range(m), 3)) for _ in range(n)]
        ok, X = check_rank(alg, n, m, rank)
        if not ok:
            badp += 1
            if firstp is None or (n, m) < firstp[:2]: firstp = (n, m, rank, X)
    for _ in range(K):
        n, m, v = rand_general(rng, maxn)
        X = alg(n, m, v)
        if X is None or None in X or not efx0(n, m, v, X):
            badg += 1
            if firstg is None or (n, m) < firstg[:2]: firstg = (n, m, v, X)
    log(f"  random n<={maxn}: {K} ranking profiles, failures {badp}; {K} general instances, failures {badg}  [{time.time() - t:.0f}s]")
    return badp, badg, firstp, firstg
