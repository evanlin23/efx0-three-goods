"""Construction LB (plan Step 2): an explicit algorithm meant to build, in any core, an EFX0 allocation in which at most
one bundle has more than two goods. Reference implementation; construct.c implements the same steps, and
construct_run.py runs it exhaustively. The written argument is in proofs/construction.md.

Input: n agents, each with its three goods ranked a > b > c (trip[i] = (a, b, c)), m goods. Output: X[g] = owner of g.

Phase 1 (serial dictatorship with an adaptive order; every pick is a singleton). Repeat until every agent has picked:
  R1 step: if some unprocessed agent has <= 2 of its goods left, the one with the smallest key
           (rank of its favourite remaining good (3 if none), number of its goods left, index) takes its favourite
           remaining good, or nothing if none is left.
  insertion: otherwise (every unprocessed agent still has all three goods), for each unprocessed agent i simulate
           "i takes a_i, then R1 steps while any apply" and count NA, the goods that some processed agent values more
           than its pick; the agent with the smallest (count, index) takes a_i.
  The goods nobody picked are the junk J. Invariants: every good an agent prefers to its pick was picked before it
  (so it is a singleton), and every junk good is worth less than the pick to every agent that values it.
Phase 2 (place the junk):
  upgrade: while some agent k holds b_k, its c_k is junk and b_k is not needed alone (b_k not in NA), give it c_k
           (k now holds {b_k, c_k}, case P, and no longer needs a_k alone; smallest k first).
  NA = goods some non-upgraded agent values more than its pick; frozen = agents whose pick is in NA (they stay
  singletons). Slots: 1 for a non-frozen, non-upgraded singleton, 2 for an empty bundle.
  If the junk fits in the slots, fill them (all bundles <= 2 goods). Otherwise, the overflow bundle: for the first
  non-frozen owner o and the first set JL of junk (lexicographic) such that JL fills o's bundle beyond its slots, the
  rest fits the other slots, and no agent k != o holding its top a_k has b_k and c_k both in o's bundle, o takes JL.
  If no such (o, JL) exists, the construction FAILS (returns None).
Soundness (proofs/construction.md): whatever it returns is EFX0 with at most one bundle of >= 3 goods. That it never
fails is the conjecture; construct_run.py checks it exhaustively on all connected cores up to a given size.
Usage: construct.py n m [m ...]   exhaustive run in Python (slow; use construct_run.py for the C version)"""
import itertools, sys, collections
PERMS = list(itertools.permutations(range(3)))

def phase1(n, m, trip):
    R = [set(t) for t in trip]
    rank = [{g: r for r, g in enumerate(t)} for t in trip]
    def r1_step(A, G, Y):
        """One R1 step in place; False if no agent is eligible."""
        best = None
        for i in sorted(A):
            left = R[i] & G
            if len(left) <= 2:
                fav = min(left, key=lambda g: rank[i][g]) if left else None
                key = (rank[i][fav] if left else 3, len(left), i)
                if best is None or key < best[0]: best = (key, i, fav)
        if best is None: return False
        _, i, fav = best
        Y[i] = fav; A.discard(i); G.discard(fav)
        return True
    def na_count(A, G, Y):
        """|NA| over the processed agents, after the upgrades already certain: a processed agent holding b_k whose
        c_k is left and valued by no unprocessed agent (so c_k will be junk), if b_k is not needed alone."""
        done = [k for k in range(n) if k not in A]
        held = {k: rank[k][Y[k]] if Y[k] is not None else 3 for k in done}
        junk = {g for g in G if not any(g in R[k] for k in A)}
        up = set()
        while True:
            NA = {g for k in done if k not in up for g in trip[k][:held[k]]}
            k = next((k for k in done if k not in up and held[k] == 1 and trip[k][2] in junk and trip[k][1] not in NA), None)
            if k is None: return len(NA)
            up.add(k); junk.discard(trip[k][2])
    A, G, Y = set(range(n)), set(range(m)), [None] * n
    while A:
        if r1_step(A, G, Y): continue
        best = None
        for i in sorted(A):
            A2, G2, Y2 = set(A), set(G), list(Y)
            Y2[i] = trip[i][0]; A2.discard(i); G2.discard(trip[i][0])
            while A2 and r1_step(A2, G2, Y2): pass
            key = (na_count(A2, G2, Y2), i)
            if best is None or key < best[0]: best = (key, i)
        i = best[1]
        Y[i] = trip[i][0]; A.discard(i); G.discard(trip[i][0])
    return Y, sorted(G)

def phase2(n, m, trip, Y, J):
    """Returns (X, owner of the large bundle or None, set of upgraded agents), or None if no placement is found."""
    rank = [{g: r for r, g in enumerate(t)} for t in trip]
    held = [rank[k][Y[k]] if Y[k] is not None else 3 for k in range(n)]
    J = set(J); up = []
    def needed():
        return {g for k in range(n) if k not in up for g in trip[k][:held[k]]}
    while True:
        NA = needed()
        k = next((k for k in range(n) if k not in up and held[k] == 1 and trip[k][2] in J and trip[k][1] not in NA), None)
        if k is None: break
        up.append(k); J.discard(trip[k][2])
    NA = needed()
    frozen = [Y[k] is not None and Y[k] in NA for k in range(n)]
    cap = [0 if frozen[k] or k in up else (1 if Y[k] is not None else 2) for k in range(n)]
    J = sorted(J)
    def build(o, JL):
        X = [None] * m
        for k in range(n):
            if Y[k] is not None: X[Y[k]] = k
        for k in up: X[trip[k][2]] = k
        for g in JL: X[g] = o
        rest = [g for g in J if g not in JL]
        for k in range(n):
            if k == o: continue
            for _ in range(cap[k]):
                if rest: X[rest.pop()] = k
        return X
    if len(J) <= sum(cap): return build(None, ()), None, set(up)
    for o in range(n):
        if frozen[o]: continue
        need = len(J) - (sum(cap) - cap[o])
        L0 = [Y[o]] if Y[o] is not None else []
        if o in up: L0.append(trip[o][2])
        for JL in itertools.combinations(J, need):
            L = set(L0) | set(JL)
            if any(k != o and held[k] == 0 and k not in up and trip[k][1] in L and trip[k][2] in L for k in range(n)):
                continue
            return build(o, JL), o, set(up)
    return None

def construct(n, m, trip):
    """Allocation X (X[g] = owner) or None if the construction fails."""
    Y, J = phase1(n, m, trip)
    res = phase2(n, m, trip, Y, J)
    return res[0] if res else None

def raw_ok(n, m, trip, X):
    """Independent check from the raw EFX0 definition under three balanced realizations of a > b > c (all must agree),
    plus at most one bundle of >= 3 goods. Does not use the T/P/B/C/E cases."""
    if X is None or len(X) != m or any(not (0 <= o < n) for o in X): return False
    bundles = [[g for g in range(m) if X[g] == j] for j in range(n)]
    if sum(len(B) >= 3 for B in bundles) > 1: return False
    res = set()
    for vals in ((4, 3, 2), (10, 9, 2), (10, 6, 5)):
        ok = True
        for i, t in enumerate(trip):
            v = dict(zip(t, vals)); own = sum(v.get(g, 0) for g in bundles[i])
            for j, B in enumerate(bundles):
                if j != i and len(B) >= 2:
                    w = [v.get(g, 0) for g in B]
                    if sum(w) - min(w) > own: ok = False
        res.add(ok)
    if len(res) != 1: raise SystemExit(f"realizations disagree (ordinality violated): {trip} {X}")
    return res.pop()

if __name__ == '__main__':
    from cores_nauty import gen_cores_nauty
    n = int(sys.argv[1])
    for m in map(int, sys.argv[2:]):
        cores = gen_cores_nauty(n, m); fails = tot = 0
        for pi, sets in cores:
            for prof in itertools.product(range(6), repeat=n):
                trip = [tuple(S[p] for p in PERMS[k]) for S, k in zip(sets, prof)]
                tot += 1
                if not raw_ok(n, m, trip, construct(n, m, trip)):
                    fails += 1
                    if fails <= 3: print(f"  FAIL {sets} profile {prof}: (a, b, c) per agent {trip}")
        print(f"n={n} m={m}: {len(cores)} cores, {tot} hypergraph-profile pairs, construction fails on {fails}", flush=True)
