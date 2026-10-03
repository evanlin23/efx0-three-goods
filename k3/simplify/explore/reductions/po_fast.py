"""H-PO on larger instances (see po_states.py for the definitions): every Pareto-optimal valid state is completable.
Faster than po_states.py: backtracking enumeration of the states, numpy dominance filter, completability checked only
for Pareto-optimal states. EVIDENCE only.
  python3 po_fast.py small N M            every ranking profile (agent 0 ranks 0 > 1 > 2)
  python3 po_fast.py sample N M K SEED    K random ranking profiles
  python3 po_fast.py cores MAXN SAMPLE    SAMPLE random profiles of every certified core with n = MAXN (lbx.core_profiles)
  python3 po_fast.py random K SEED MAXN   K random profiles, n in 2..MAXN, m in max(3, n)..2n+2
"""
import sys, os, random, time
import numpy as np
from engine import gen_small, NA
from po_states import completable
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))

def states(rank, m):
    n = len(rank); out = []; Y = [None] * n; U = []; u = [0] * n; used = set()
    def rec(i):
        if i == n:
            na = NA(rank, Y, U)
            singles = {Y[j] for j in range(n) if j not in U and Y[j] is not None}
            if na <= singles and not any(rank[x][1] in na or rank[x][2] in na for x in U):
                out.append((list(Y), list(U), tuple(u)))
            return
        a, b, c = rank[i]
        Y[i] = None; u[i] = 0; rec(i + 1)
        for t, g in enumerate((a, b, c)):
            if g not in used:
                used.add(g); Y[i] = g; u[i] = 3 - t; rec(i + 1); used.discard(g)
        if b not in used and c not in used:
            used.update((b, c)); Y[i] = b; U.append(i); u[i] = 4; rec(i + 1); U.pop(); used.difference_update((b, c))
        Y[i] = None; u[i] = 0
    rec(0)
    return out

def pareto(us):
    A = np.array(us, dtype=np.int8); S = len(A); keep = np.ones(S, bool); s = A.sum(1)
    for k in range(S):
        ge = (A >= A[k]).all(1) & (s > s[k])
        if ge.any(): keep[k] = False
    return np.nonzero(keep)[0]

def check(rank, m):
    """returns (#valid states, #PO states, first PO state that is not completable or None)"""
    S = states(rank, m); po = pareto([u for _, _, u in S])
    for k in po:
        Y, U, _ = S[k]
        if not completable(rank, m, Y, U): return len(S), len(po), (Y, U)
    return len(S), len(po), None

def run(src, label):
    t = time.time(); tot = bad = 0; first = None; mxS = 0
    for rank, m in src:
        tot += 1; nS, nP, b = check(rank, m); mxS = max(mxS, nS)
        if b is not None:
            bad += 1
            if first is None: first = (rank, m, b)
    print(f"{label}: {tot} profiles; some PO valid state not completable on {bad}; first {first}; max #valid states {mxS}  [{time.time() - t:.0f}s]", flush=True)

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'small':
        n, m = int(sys.argv[2]), int(sys.argv[3])
        run(((r, m) for r in gen_small(n, m)), f"every profile n={n} m={m}")
    elif mode == 'sample':
        n, m, K, seed = map(int, sys.argv[2:6]); rng = random.Random(seed)
        run((([(0, 1, 2)] + [tuple(rng.sample(range(m), 3)) for _ in range(n - 1)], m) for _ in range(K)),
            f"{K} random profiles n={n} m={m} (seed {seed})")
    elif mode == 'cores':
        from lbx import core_profiles
        N, S = int(sys.argv[2]), int(sys.argv[3])
        run(((list(r), m) for _, m, r in core_profiles(N, sample=S, minn=N)), f"cores n={N}, {S} random profiles per core")
    elif mode == 'random':
        K, seed, N = map(int, sys.argv[2:5]); rng = random.Random(seed)
        def gen():
            for _ in range(K):
                n = rng.randint(2, N); m = rng.randint(max(3, n), 2 * n + 2)
                yield [tuple(rng.sample(range(m), 3)) for _ in range(n)], m
        run(gen(), f"{K} random profiles n<={N}, m in max(3,n)..2n+2 (seed {seed})")
