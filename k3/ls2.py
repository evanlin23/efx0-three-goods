"""Algorithm LS2 of proofs/local_search.md §4 (Theorem C), a polynomial-time implementation written from the text.

For timings and for the comparison with K3ALG (proofs/k3_algorithm.md §9). Every choice is the first one in index
order; envy paths are found by breadth-first search, systems of distinct representatives and maximum matchings by
augmenting paths. `ls2(n, m, v)` takes a *core* (every agent values exactly three goods, is balanced, and every good
is valued by some agent; at most one private good per agent) with numeric values, decides everything numerically,
and returns (X, info) with X[g] the owner of good g. The referee `k3/ls2_referee.py` checks the claims of the proof
independently; this file is not part of that check.

Cost per Phase-1 step: O(n + m) for the envy graph and steps 1-5 (each agent compares only the at most three
bundles holding its goods), O(n (n + m)) for step 6 (a breadth-first search per dirty triple) and O(n (n + m)) for
step 7 and Phase 2 (augmenting paths); at most 7n steps (Theorem C). So O(n^2 (n + m)) in all, written analysis.

Usage: python3 k3/ls2.py --random N [--seed=S]   N random cores: output complete, raw EFX0, <= 1 large bundle
"""
import sys, os, random, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k3algo import raw_efx0

POOL = -1

def ls2(n, m, v):
    rank = []
    for i in range(n):
        gs = sorted(v[i], key=lambda g: (-v[i][g], g))      # strict ranking: ties broken by index (L5 (iv))
        assert len(gs) == 3 and v[i][gs[0]] < v[i][gs[1]] + v[i][gs[2]]
        rank.append(tuple(gs))
    # strict values used for all decisions: ranks, realized as (4, 3, 2)
    w = [{rank[i][0]: 4, rank[i][1]: 3, rank[i][2]: 2} for i in range(n)]
    valuers = [[] for _ in range(m)]
    for i in range(n):
        for g in rank[i]: valuers[g].append(i)
    own = [POOL] * m
    B = [set() for _ in range(n)]
    info = collections.Counter()

    def val(i, S): return sum(w[i].get(g, 0) for g in S)

    def give(takes):
        for i in takes:
            for g in B[i]: own[g] = POOL
            B[i] = set()
        for i, T in takes.items():
            for g in T:
                assert own[g] == POOL
                own[g] = i
            B[i] = set(T)

    steps = 0
    while True:
        U = [g for g in range(m) if own[g] == POOL]
        if not U: return own, dict(info, steps=steps, phase2='none')
        vown = [val(i, B[i]) for i in range(n)]
        # envy graph: i can envy only the (at most three) holders of its goods
        env = [set() for _ in range(n)]; envied = [False] * n
        for i in range(n):
            for j in {own[g] for g in rank[i] if own[g] != POOL and own[g] != i}:
                if val(i, B[j]) > vown[i]: env[i].add(j); envied[j] = True
        # step 1
        s1 = next(((i, u) for u in U for i in valuers[u] if w[i][u] > vown[i]), None)
        if s1:
            i, u = s1; give({i: {u}}); steps += 1; info['step1'] += 1; continue
        # step 2: an envy cycle (iterative DFS)
        color = [0] * n; parent = [-1] * n; cyc = None
        for r in range(n):
            if color[r] or cyc: continue
            stack = [(r, iter(sorted(env[r])))]; color[r] = 1
            while stack and not cyc:
                x, it = stack[-1]
                nxt = next(it, None)
                if nxt is None: color[x] = 2; stack.pop(); continue
                if color[nxt] == 0:
                    color[nxt] = 1; parent[nxt] = x; stack.append((nxt, iter(sorted(env[nxt]))))
                elif color[nxt] == 1:
                    c = [x]
                    while c[-1] != nxt: c.append(parent[c[-1]])
                    cyc = c[::-1]                                  # nxt -> ... -> x -> nxt
        if cyc:
            L = len(cyc)
            give({cyc[t]: B[cyc[(t + 1) % L]] & set(rank[cyc[t]]) for t in range(L)})
            steps += 1; info['step2'] += 1; continue
        Uset = set(U)
        aholder = [i for i in range(n) if B[i] == {rank[i][0]}]
        # step 3
        s3 = next((i for i in aholder if rank[i][1] in Uset and rank[i][2] in Uset), None)
        if s3 is not None:
            i = s3; give({i: {rank[i][1], rank[i][2]}}); steps += 1; info['step3'] += 1; continue
        # step 4
        s4 = next(((i, u) for i in aholder if not envied[i] and ((rank[i][1] in Uset) != (rank[i][2] in Uset))
                   for u in rank[i][1:] if u in Uset), None)
        if s4:
            i, u = s4; give({i: {rank[i][0], u}}); steps += 1; info['step4'] += 1; continue
        onegood = [s for s in range(n) if not envied[s] and len(B[s]) == 1]
        # step 5
        s5 = next(((s, u) for s in onegood for u in rank[s] if u in Uset), None)
        if s5:
            s, u = s5; give({s: B[s] | {u}}); steps += 1; info['step5'] += 1; continue
        empty = [e for e in range(n) if not B[e]]
        if empty:                                          # Phase 2 (a)
            for u in U: own[u] = empty[0]
            return own, dict(info, steps=steps, phase2='a')
        # dirty triples and D(s)
        holder_of = {next(iter(B[s])): s for s in onegood}
        dirty = []                                          # (i, u, s)
        for i in aholder:
            b, c = rank[i][1], rank[i][2]
            for u, y in ((b, c), (c, b)):
                if u in Uset and y in holder_of: dirty.append((i, u, holder_of[y]))
        D = collections.defaultdict(set)
        for i, u, s in dirty: D[s].add(u)
        def bfs_path(s, t):
            prev = {s: None}; q = collections.deque([s])
            while q:
                x = q.popleft()
                if x == t: break
                for y in sorted(env[x]):
                    if y not in prev: prev[y] = x; q.append(y)
            if t not in prev or t == s: return None
            p = [t]
            while p[-1] != s: p.append(prev[p[-1]])
            return p[::-1]
        # step 6
        s6 = None
        for i, u, s in dirty:
            P = bfs_path(s, i)
            if P: s6 = (i, u, s, P); break
        if s6:
            i, u, s, P = s6
            takes = {P[q]: B[P[q + 1]] & set(rank[P[q]]) for q in range(len(P) - 1)}
            takes[i] = {u} | B[s]
            give(takes); steps += 1; info['step6'] += 1; continue
        # maximum matching between one-good sources and goods (s - u iff u in D(s))
        match_s, match_u = {}, {}
        def augment(s, seen):
            for u in sorted(D[s]):
                if u in seen: continue
                seen.add(u)
                if u not in match_u or augment(match_u[u], seen):
                    match_s[s] = u; match_u[u] = s; return True
            return False
        for s in onegood: augment(s, set())
        if len(match_s) == len(onegood):
            # step 7: the augmented envy cycle of Claim 3, with the SDR ell = match_s
            ell = match_s; ch = {}
            for s in onegood:
                i = next(i for i, u, s2 in dirty if s2 == s and u == ell[s])
                # a one-good source f != s with an envy path to i (Claim 2 (h)): reverse BFS from i
                rev = collections.defaultdict(list)
                for x in range(n):
                    for y in env[x]: rev[y].append(x)
                prev = {i: None}; q = collections.deque([i]); f = None
                while q:
                    x = q.popleft()
                    if x in holder_of.values() and x != s and len(B[x]) == 1 and not envied[x]: f = x; break
                    for y in sorted(rev[x]):
                        if y not in prev: prev[y] = x; q.append(y)
                assert f is not None, "Claim 2 (h) fails"
                P = [f]
                while P[-1] != i: P.append(prev[P[-1]])
                ch[s] = (i, f, P)
            s0 = onegood[0]; seen = []
            while s0 not in seen: seen.append(s0); s0 = ch[s0][1]
            cycf = seen[seen.index(s0):]; k = len(cycf)
            W = [cycf[0]]; lab = []
            for j in range(k - 1, -1, -1):
                sj = cycf[j]; i_s, fs, P = ch[sj]
                for q2 in range(1, len(P)): W.append(P[q2]); lab.append(None)
                W.append(sj); lab.append(sj)
            last = {}; best = None
            for t, x in enumerate(W):
                if x in last and (best is None or t - last[x] < best[1] - best[0]): best = (last[x], t)
                last[x] = t
            p, q2 = best
            takes = {}
            for t in range(p, q2):
                a_, b_ = W[t], W[t + 1]
                takes[a_] = (B[b_] & set(rank[a_])) if lab[t] is None else ({ell[lab[t]]} | B[lab[t]])
            give(takes); steps += 1; info['step7'] += 1; continue
        # Phase 2 (b)
        sstar = next(s for s in onegood if s not in match_s)
        T = {sstar}; fr = [sstar]
        while fr:
            s = fr.pop()
            for u in D[s]:
                if u in match_u and match_u[u] not in T: T.add(match_u[u]); fr.append(match_u[u])
        DT = set().union(*[D[s] for s in T])
        for u in U: own[u] = match_u[u] if u in DT else sstar
        return own, dict(info, steps=steps, phase2='b')

def random_true_core(n, rng, vmax=100, levels=False):
    """A random core: every agent values three goods and is balanced; every good is valued; at most one private good
    per agent. m is about 3n/2."""
    while True:
        npriv = rng.randint(0, n // 4)
        slots = 3 * n - npriv
        nshared = rng.randint(max(1, slots // 3), slots // 2)
        # shared goods: degrees >= 2 summing to `slots`
        deg = [2] * nshared
        for _ in range(slots - 2 * nshared): deg[rng.randrange(nshared)] += 1
        pool = [g for g in range(nshared) for _ in range(deg[g])]
        rng.shuffle(pool)
        sets = [[] for _ in range(n)]
        privs = rng.sample(range(n), npriv)
        for t, i in enumerate(privs): sets[i].append(nshared + t)
        ok = True
        for i in range(n):
            while len(sets[i]) < 3:
                if not pool: ok = False; break
                g = pool.pop()
                if g in sets[i]: ok = False; break
                sets[i].append(g)
        if not ok or pool: continue
        m = nshared + npriv
        v = []
        for i in range(n):
            if levels:
                x = rng.choice([(3, 2, 2), (4, 3, 2), (2, 2, 2), (5, 4, 2), (3, 3, 2)])
            else:
                while True:
                    x = sorted((rng.randint(1, vmax) for _ in range(3)), reverse=True)
                    if x[0] < x[1] + x[2]: break
            gs = sets[i][:]; rng.shuffle(gs)
            v.append(dict(zip(gs, x)))
        return n, m, v

if __name__ == '__main__':
    args = sys.argv[1:]
    opt = {a.split('=')[0]: a.split('=')[1] for a in args if '=' in a}
    if '--random' in args:
        N = int([a for a in args if a.isdigit()][0]); rng = random.Random(int(opt.get('--seed', 1)))
        tally = collections.Counter(); maxsteps = 0
        for t in range(N):
            n = rng.randint(2, 40)
            n, m, v = random_true_core(n, rng, levels=(t % 2 == 1))
            X, info = ls2(n, m, v)
            ok = raw_efx0(n, m, v, X) and all(o != POOL for o in X)
            big = sum(1 for s in collections.Counter(X).values() if s > 2)
            if not ok or big > 1 or info['steps'] > 7 * n:
                print("FAIL", n, m, v, X, info); sys.exit(1)
            tally[info['phase2']] += 1; maxsteps = max(maxsteps, info['steps'] / n)
            for k in ('step6', 'step7'): tally[k] += info.get(k, 0)
        print(f"ls2 --random {N}: every output complete, raw EFX0, at most one bundle of > 2 goods, Phase 1 <= 7n steps; "
              f"{dict(tally)}; largest steps/n {maxsteps:.2f}")
