#!/usr/bin/env python3
"""Referee check of Theorem VM (k4/vm.md §8, branch claude/k4-vm), written independently.

Implements the Viswanathan-Mehta 4-limited algorithm from the AAMAS 2024 abstract's text, under the reading
of k4/vm.md §2 (global ranks, ties by good index; only the *matched* Phase-I agents leave N^r; Phase-I winners
are nodes of the EFX graph), and enumerates every resolution of its choice points:
  - which claimant wins each contested good in each maximum matching (Phase I, Phase II k = 1..4, Phase III a, b, c),
  - the order in which unassigned valued goods are processed in the EFX-graph step,
  - which source receives the good,
  - which agent receives the junk.
At every EFX-graph step it records whether the graph is acyclic, its longest directed path, whether a source
exists, and whether some valuer of j lies outside S = W ∪ N1 ∪ N2r. After every step it checks ordinary EFX of
the partial allocation from the raw definition; at the end it checks completeness and ordinary EFX.
Shares no code with k4/vm/.

Raw definitions used:
  ordinary EFX: for all i != j, every g in X_j with v_i(g) > 0: v_i(X_i) >= v_i(X_j - g).
  EFX0:         the same for every g in X_j.
"""
import itertools, random, sys, json, os
VARIANT = os.environ.get('VM_VARIANT', '')
from collections import defaultdict

def val(v, i, S):
    return sum(v[i][g] for g in S)

def efx_ok(v, X, zero=False):
    n = len(X)
    for i in range(n):
        vi = val(v, i, X[i])
        for j in range(n):
            if i == j:
                continue
            tot = val(v, i, X[j])
            for g in X[j]:
                if (zero or v[i][g] > 0) and tot - v[i][g] > vi:
                    return False
    return True

def ranking(v, i):
    R = [g for g in range(len(v[i])) if v[i][g] > 0]
    R.sort(key=lambda g: (-v[i][g], g))
    return R

def r(rk, i, k):  # k is 1-based
    return rk[i][k - 1] if len(rk[i]) >= k else None

def matchings(claims):
    """claims: dict good -> list of claimant agents (each agent claims <= 1 good).
    A maximum matching gives each claimed good to one claimant; yield every such choice."""
    goods = sorted(claims)
    for pick in itertools.product(*[claims[g] for g in goods]):
        yield list(zip(goods, pick))

class Stats:
    def __init__(self):
        self.runs = 0; self.not_efx = 0; self.incomplete = 0; self.stuck = 0; self.cyclic = 0
        self.maxpath = 0; self.outside = 0; self.partial_bad = 0; self.capped = 0
        self.examples = []

def longest_path(nodes, edges):
    # returns (acyclic, longest path length in edges)
    adj = defaultdict(list)
    for a, b in edges:
        adj[a].append(b)
    state = {}; memo = {}
    def dfs(u):
        if state.get(u) == 1:
            raise ValueError("cycle")
        if u in memo:
            return memo[u]
        state[u] = 1
        best = 0
        for w in adj[u]:
            best = max(best, 1 + dfs(w))
        state[u] = 2; memo[u] = best
        return best
    try:
        return True, max([dfs(u) for u in nodes] + [0])
    except ValueError:
        return False, None

def efx_graph(v, X, j, S):
    nodes = [i for i in S if v[i][j] > 0]
    edges = []
    for i in nodes:
        vi = val(v, i, X[i])
        for ip in nodes:
            if ip == i:
                continue
            B = X[ip] | {j}
            tot = val(v, i, B)
            if any(v[i][h] > 0 and tot - v[i][h] > vi for h in B):
                edges.append((i, ip))
    return nodes, edges

def run_all(v, cap=None, rng=None, st=None, check_partial=True, aout='matched'):
    n = len(v); m = len(v[0])
    rk = [ranking(v, i) for i in range(n)]
    def vr(i, k):
        g = r(rk, i, k)
        return v[i][g] if g is not None else 0
    A = [i for i in range(n) if vr(i, 1) > vr(i, 2) + vr(i, 3)]
    if st is None:
        st = Stats()
    budget = [cap]

    def finish(X, unassigned, S, tag):
        # EFX-graph step: recursive over choice of j and source
        valued = [g for g in unassigned if any(v[i][g] > 0 for i in range(n))]
        if not valued:
            junk = [g for g in unassigned]
            # junk to an arbitrary agent: every choice
            recipients = range(n) if junk else [None]
            for a in recipients:
                if budget[0] is not None and budget[0] <= 0:
                    st.capped += 1; return
                Y = [set(b) for b in X]
                if a is not None:
                    Y[a] |= set(junk)
                st.runs += 1
                if budget[0] is not None:
                    budget[0] -= 1
                if sorted(g for b in Y for g in b) != list(range(m)):
                    st.incomplete += 1
                if not efx_ok(v, Y):
                    st.not_efx += 1
                    if len(st.examples) < 5:
                        st.examples.append(("not_efx", v, [sorted(b) for b in Y], tag))
            return
        order = valued if rng is None else rng.sample(valued, len(valued))
        for j in order:
            outside = [i for i in range(n) if v[i][j] > 0 and i not in S]
            if outside:
                st.outside += 1
            nodes, edges = efx_graph(v, X, j, S)
            ac, lp = longest_path(nodes, edges)
            if not ac:
                st.cyclic += 1
                if len(st.examples) < 5:
                    st.examples.append(("cyclic", v, [sorted(b) for b in X], j))
            else:
                st.maxpath = max(st.maxpath, lp)
            haveIn = {b for a, b in edges}
            sources = [i for i in nodes if i not in haveIn]
            if not sources:
                st.stuck += 1
                continue
            for s in (sources if rng is None else [rng.choice(sources)]):
                Y = [set(b) for b in X]; Y[s].add(j)
                if check_partial and not efx_ok(v, Y):
                    st.partial_bad += 1
                    if len(st.examples) < 5:
                        st.examples.append(("partial", v, [sorted(b) for b in Y], j))
                finish(Y, unassigned - {j}, S, tag)
                if budget[0] is not None and budget[0] <= 0:
                    return
            if rng is not None:
                return

    # Phase I
    claimsI = defaultdict(list)
    for i in A:
        claimsI[r(rk, i, 1)].append(i)
    for mI in matchings(claimsI):
        X = [set() for _ in range(n)]
        un = set(range(m))
        W = set()
        for g, i in mI:
            X[i].add(g); un.discard(g); W.add(i)
        Nr = set(range(n)) - (W if aout == 'matched' else set(A))
        phase2(v, rk, X, un, W, Nr, 1, {}, finish, budget, st)
        if budget[0] is not None and budget[0] <= 0:
            break
    return st

def phase2(v, rk, X, un, W, Nr, k, stage, finish, budget, st):
    n = len(v)
    if k == 5:
        phase3(v, rk, X, un, W, stage, finish, budget, st)
        return
    claims = defaultdict(list)
    for i in sorted(Nr):
        g = r(rk, i, k)
        if g is not None and g in un:
            claims[g].append(i)
    for mt in matchings(claims):
        Y = [set(b) for b in X]; un2 = set(un); stage2 = dict(stage); Nr2 = set(Nr)
        for g, i in mt:
            Y[i].add(g); un2.discard(g); stage2[i] = k; Nr2.discard(i)
        if not efx_ok(v, Y):
            st.partial_bad += 1
        phase2(v, rk, Y, un2, W, Nr2, k + 1, stage2, finish, budget, st)
        if budget[0] is not None and budget[0] <= 0:
            return

def phase3(v, rk, X, un, W, stage, finish, budget, st):
    N1 = {i for i, s in stage.items() if s == 1}
    N2 = {i for i, s in stage.items() if s == 2}
    N3 = {i for i, s in stage.items() if s == 3}
    steps = [(N3, 4), (N2, 3), (None, 4)]   # None: N2 minus N2r
    if VARIANT == 'n2first':   # mutation: serve N2 (3rd, then 4th choices) before N3
        steps = [(N2, 3), (None, 4), (N3, 4)]
    def rec(idx, X, un, N2r):
        if idx == 3:
            S = set(W) | N1 | N2r
            if VARIANT == 'noW':   # mutation: Phase-I winners are not EFX-graph nodes
                S = N1 | N2r
            finish(X, un, S, "run")
            return
        grp, kk = steps[idx]
        if grp is None:
            grp = N2 - N2r
        claims = defaultdict(list)
        for i in sorted(grp):
            g = r(rk, i, kk)
            if g is not None and g in un:
                claims[g].append(i)
        for mt in matchings(claims):
            Y = [set(b) for b in X]; un2 = set(un); N2r2 = set(N2r)
            for g, i in mt:
                Y[i].add(g); un2.discard(g)
                if (idx == 1 and VARIANT != 'n2first') or (idx == 0 and VARIANT == 'n2first'):
                    N2r2.add(i)
            if not efx_ok(v, Y):
                st.partial_bad += 1
            rec(idx + 1, Y, un2, N2r2)
            if budget[0] is not None and budget[0] <= 0:
                return
    rec(0, X, un, set())

def report(name, st, ninst):
    d = dict(source=name, instances=ninst, runs=st.runs, capped=st.capped, not_efx=st.not_efx,
             incomplete=st.incomplete, stuck=st.stuck, cyclic=st.cyclic, max_path_edges=st.maxpath,
             valuer_outside_S=st.outside, partial_not_efx=st.partial_bad)
    print(json.dumps(d)); sys.stdout.flush()
    for e in st.examples:
        print("EXAMPLE", e)
    return d

def exhaustive(n, m, vals, cap=None):
    st = Stats(); cnt = 0
    for flat in itertools.product(vals, repeat=n * m):
        v = [list(flat[i * m:(i + 1) * m]) for i in range(n)]
        if any(sum(1 for x in row if x > 0) > 4 for row in v):
            continue
        cnt += 1
        run_all(v, cap=cap, st=st)
    return report(f"exhaustive n={n} m={m} vals={list(vals)}", st, cnt)

def rand_inst(rng, n, m, maxv, pzero_agent=0.0):
    v = []
    for i in range(n):
        k = rng.randint(0, min(4, m))
        R = rng.sample(range(m), k)
        row = [0] * m
        for g in R:
            row[g] = rng.randint(1, maxv)
        # sometimes make top-heavy
        if R and rng.random() < 0.3:
            row[R[0]] = sum(row) + rng.randint(1, maxv)
        v.append(row)
    return v

def random_test(N, nmax, mmax, maxv, seed, cap):
    rng = random.Random(seed); st = Stats()
    for t in range(N):
        n = rng.randint(2, nmax); m = rng.randint(1, mmax)
        v = rand_inst(rng, n, m, maxv)
        run_all(v, cap=cap, st=st)
    return report(f"random N={N} n<={nmax} m<={mmax} maxv={maxv} seed={seed} cap={cap}", st, N)

def contested(N, seed, cap):
    """Adversarial family: few goods, many agents, all 4-limited, heavy overlap of tops and second goods,
    many top-heavy agents (so W, N1, N2r all populated)."""
    rng = random.Random(seed); st = Stats()
    for t in range(N):
        n = rng.randint(3, 6); m = rng.randint(4, 8)
        v = []
        for i in range(n):
            R = rng.sample(range(min(m, 5)), min(4, min(m, 5))) if rng.random() < 0.7 else rng.sample(range(m), min(4, m))
            row = [0] * m
            base = sorted([rng.randint(1, 6) for _ in R], reverse=True)
            for g, x in zip(R, base):
                row[g] = x
            if rng.random() < 0.5:
                row[R[0]] = base[1] + base[2] + rng.randint(1, 3) if len(base) >= 3 else row[R[0]] + 5
            v.append(row)
        run_all(v, cap=cap, st=st)
    return report(f"contested N={N} seed={seed} cap={cap}", st, N)

if __name__ == "__main__":
    which = sys.argv[1]
    if which == "exh":
        n, m, mv = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        exhaustive(n, m, range(mv + 1), cap=int(sys.argv[5]) if len(sys.argv) > 5 else None)
    elif which == "rand":
        random_test(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]), int(sys.argv[7]))
    elif which == "cont":
        contested(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
    elif which == "lit":
        # literal reading (all of A leaves N^r) on the n = 2, m = 2 instance of k4/vm.md §4.2
        v = [[13, 8], [7, 2]]
        for a in ("all", "matched"):
            report(f"n=2 m=2 {v} aout={a}", run_all(v, aout=a), 1)
        # Example 2.1 of the abstract: EFX graph for d with A->a, B->b, C->c
        v = [[2, 1, 3, 1], [1, 3, 2, 4], [1, 2, 3, 4]]
        X = [{0}, {1}, {2}]
        print("Example 2.1 edges:", efx_graph(v, X, 3, [0, 1, 2])[1])
