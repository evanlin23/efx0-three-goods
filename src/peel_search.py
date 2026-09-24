"""Step 2 exploration: which EFX0 allocations can peeling (L2) plus insertion (L10) reach? Exhaustive over the choices.
A run processes agents one at a time on the remaining goods:
  R1: an agent with <= 2 remaining relevant goods takes its favourite remaining one as a singleton (or nothing);
  insertion: when every remaining agent still has all 3 goods (a core state), some agent takes {a} (its top).
Every bundle so far is a singleton or empty, and each agent is safe: the goods it prefers to its bundle were allocated
before it, as singletons, and at most one worse good of it remains. Goods left at the end ("junk") are worth less to
every agent that values them than that agent's bundle. Two ways to place them:
  PID (--dump): all junk into one bundle (L2's "the last agent takes everything", with a free choice of owner);
  PIJ (default): junk fills free slots first (an empty bundle takes 2, a singleton {g} that nobody needs alone takes 1),
       and only the overflow goes into one large bundle, whose owner o and contents are searched.
The final allocation is checked with the L5 model (any bundle sizes) and must have at most one bundle of >= 3 goods.
Usage: peel_search.py n m [m ...] [--dump]   prints, per (n, m), the ranking profiles on which no run succeeds"""
import itertools, sys, collections
from cores_nauty import gen_cores_nauty
PERMS = list(itertools.permutations(range(3)))

def unsafe(n, trip, X):
    """Agents that are not safe in allocation X (X[g] = owner of good g), by L5's cases T/P/B/C/E."""
    size = collections.Counter(X)
    alone = lambda g: size[X[g]] == 1
    bad = []
    for i, (a, b, c) in enumerate(trip):
        ok = ((X[a] == i and (X[b] == i or X[c] == i)) or (X[a] == i and not (X[b] == X[c] and size[X[b]] >= 3))
              or (X[b] == i and X[c] == i) or (X[b] == i and alone(a)) or (X[c] == i and alone(a) and alone(b))
              or (alone(a) and alone(b) and alone(c)))
        if not ok: bad.append(i)
    return bad

def nlarge(X):
    return sum(1 for v in collections.Counter(X).values() if v >= 3)

def place_junk(n, m, trip, bundles, J, dump):
    """Complete the pre-junk allocation `bundles` by placing the junk goods J; None if no placement works."""
    rank = [{g: r for r, g in enumerate(t)} for t in trip]
    held = [min((rank[k][g] for g in bundles[k] if g in rank[k]), default=3) for k in range(n)]
    NA = {g for k in range(n) for g in trip[k][:held[k]] if g not in bundles[k]}      # goods someone needs alone
    slot = [0] * n if dump else [2 if not B else (1 if len(B) == 1 and B[0] not in NA else 0) for B in bundles]
    J = sorted(J)
    def build(o, JL):
        X = [None] * m
        for j in range(n):
            for g in bundles[j]: X[g] = j
        for g in JL: X[g] = o
        rest = [g for g in J if g not in JL]
        for j in range(n):
            for _ in range(slot[j] if j != o else 0):
                if rest: X[rest.pop()] = j
        return None if rest else X
    if len(J) <= sum(slot): return build(None, ())
    for o in range(n):
        need = len(J) - (sum(slot) - slot[o])
        for JL in itertools.combinations(J, need):
            X = build(o, JL)
            if X is not None and nlarge(X) <= 1 and not unsafe(n, trip, X): return X
    return None

def search(n, m, trip, dump=False):
    """Some successful run (its allocation), or None. Branches over the agent processed at every step."""
    R = [set(t) for t in trip]
    rank = [{g: r for r, g in enumerate(t)} for t in trip]
    def rec(ragents, rgoods, bundles):
        if not ragents: return place_junk(n, m, trip, bundles, rgoods, dump)
        elig = [i for i in ragents if len(R[i] & rgoods) <= 2]
        for i in (elig or sorted(ragents)):
            b = sorted(R[i] & rgoods, key=lambda g: rank[i][g])[:1] if elig else [trip[i][0]]
            nb = list(bundles); nb[i] = b
            X = rec(ragents - {i}, rgoods - set(b), nb)
            if X is not None: return X
        return None
    return rec(frozenset(range(n)), frozenset(range(m)), [[] for _ in range(n)])

if __name__ == '__main__':
    n = int(sys.argv[1]); ms = [int(a) for a in sys.argv[2:] if not a.startswith('--')]; dump = '--dump' in sys.argv
    for m in ms:
        cores = gen_cores_nauty(n, m); fails = tot = 0
        for pi, sets in cores:
            f = 0
            for prof in itertools.product(range(6), repeat=n):
                trip = [tuple(S[p] for p in PERMS[k]) for S, k in zip(sets, prof)]
                tot += 1; X = search(n, m, trip, dump)
                if X is None:
                    f += 1
                    if f == 1: print(f"  first failure: {sets} profile {prof}, (a, b, c) per agent: {trip}")
                else: assert nlarge(X) <= 1 and not unsafe(n, trip, X)
            fails += f
        print(f"n={n} m={m}: {len(cores)} cores, {tot} hypergraph-profile pairs, "
              f"{'PID' if dump else 'PIJ'} fails on {fails}", flush=True)
