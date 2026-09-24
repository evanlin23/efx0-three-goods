"""Construction LB+ (proofs/lb_last_step.md), reference implementation in Python, written from the proof and separately
from lbplus.c. Phase 1: LB's (construct.py's phase1) or every sequence of insertion choices with LB's R1 order. Phase 2:
LB's upgrades; then no owner (omega <= 0), owner r (Lemma 1 with one good per exposed pair, a common good when pairs
meet), or the rotation of Theorem B and owner k. Every output is checked with construct.raw_ok (raw EFX0 definition,
three balanced realizations, at most one bundle of >= 3 goods).
Usage: lbplus.py n [m ...] [--mode=0|1]      tallies per (n, m): runs, c2, owner_r, rotated, rot_c2, rot_owner_k,
                                             failures (compare with lbplus.c: lb_owner.py n --bin=lbplus --mode=M)"""
import sys, itertools, collections
from construct import phase1 as lb_phase1, raw_ok, PERMS
from cores_nauty import gen_cores_nauty
from frontier import options

def runs_all(n, m, trip):
    """Every run of Phase 1 over all insertion choices, LB's R1 order: yields (Y, order, leader flags)."""
    R = [set(t) for t in trip]; rank = [{g: r for r, g in enumerate(t)} for t in trip]
    def rec(A, G, Y, order, ins):
        A, G, Y, order, ins = set(A), set(G), list(Y), list(order), list(ins)
        while A:
            best = None
            for i in sorted(A):
                left = R[i] & G
                if len(left) <= 2:
                    fav = min(left, key=lambda g: rank[i][g]) if left else None
                    key = (rank[i][fav] if left else 3, len(left), i)
                    if best is None or key < best[0]: best = (key, i, fav)
            if best is None: break
            _, i, fav = best; Y[i] = fav; A.discard(i); G.discard(fav); order.append(i); ins.append(False)
        if not A: yield Y, order, ins; return
        for i in sorted(A):
            Y2 = list(Y); Y2[i] = trip[i][0]
            yield from rec(A - {i}, G - {trip[i][0]}, Y2, order + [i], ins + [True])
    yield from rec(set(range(n)), set(range(m)), [None] * n, [], [])

def lb_run(n, m, trip):
    """LB's own Phase 1: construct.py's phase1 with the processing order recorded (same steps; the picks are asserted
    equal to construct.phase1's)."""
    R = [set(t) for t in trip]; rank = [{g: r for r, g in enumerate(t)} for t in trip]
    def r1_step(A, G, Y, order, ins):
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
        if order is not None: order.append(i); ins.append(False)
        return True
    def na_count(A, G, Y):
        done = [k for k in range(n) if k not in A]
        held = {k: rank[k][Y[k]] if Y[k] is not None else 3 for k in done}
        junk = {g for g in G if not any(g in R[k] for k in A)}
        up = set()
        while True:
            NA = {g for k in done if k not in up for g in trip[k][:held[k]]}
            k = next((k for k in done if k not in up and held[k] == 1 and trip[k][2] in junk and trip[k][1] not in NA), None)
            if k is None: return len(NA)
            up.add(k); junk.discard(trip[k][2])
    A, G, Y, order, ins = set(range(n)), set(range(m)), [None] * n, [], []
    while A:
        if r1_step(A, G, Y, order, ins): continue
        best = None
        for i in sorted(A):
            A2, G2, Y2 = set(A), set(G), list(Y)
            Y2[i] = trip[i][0]; A2.discard(i); G2.discard(trip[i][0])
            while A2 and r1_step(A2, G2, Y2, None, None): pass
            key = (na_count(A2, G2, Y2), i)
            if best is None or key < best[0]: best = (key, i)
        i = best[1]
        Y[i] = trip[i][0]; A.discard(i); G.discard(trip[i][0]); order.append(i); ins.append(True)
    assert Y == lb_phase1(n, m, trip)[0]
    return Y, order, ins

def lbplus(n, m, trip, Y, order, ins):
    """Returns (allocation X as owner per good, tag)."""
    rank = [{g: r for r, g in enumerate(t)} for t in trip]
    a = [t[0] for t in trip]; b = [t[1] for t in trip]; c = [t[2] for t in trip]
    picked = {g for g in Y if g is not None}
    J = set(range(m)) - picked
    U = set()
    def needs(i, Yv):
        return set(trip[i]) if Yv[i] is None else {g for g in trip[i] if rank[i][g] < rank[i][Yv[i]]}
    def NAof(Yv, Uv): return set().union(*[needs(i, Yv) for i in range(n) if i not in Uv])
    while True:                                               # LB's upgrades (any order gives (UT))
        NA = NAof(Y, U)
        k = next((k for k in range(n) if k not in U and Y[k] == b[k] and c[k] in J and b[k] not in NA), None)
        if k is None: break
        U.add(k); J.discard(c[k])
    def state(Yv, Uv, Jv):
        NA = NAof(Yv, Uv)
        assert not (Jv & NA) and all(b[u] not in NA and c[u] not in NA and Yv[u] == b[u] for u in Uv), "invalid"
        F = {i for i in range(n) if i not in Uv and Yv[i] is not None and Yv[i] in NA}
        cap = [0 if i in Uv or i in F else (1 if Yv[i] is not None else 2) for i in range(n)]
        return NA, F, cap
    def base(i, Yv, Uv):
        return ({b[i], c[i]} if i in Uv else ({Yv[i]} if Yv[i] is not None else set()))
    def exposed(o, Yv, Uv, Jv):
        B0 = base(o, Yv, Uv)
        return [x for x in range(n) if x != o and x not in Uv and Yv[x] == a[x] and {b[x], c[x]} <= Jv | B0]
    def complete(Yv, Uv, Jv, cap, o, H):
        X = [None] * m
        for i in range(n):
            for g in base(i, Yv, Uv): X[g] = i
        slots = sum(cap) - (cap[o] if o is not None else 0)
        C = list(H) + [g for g in sorted(Jv) if g not in H]
        C, rest = C[:slots], C[slots:]
        for i in range(n):
            if i == o: continue
            for _ in range(cap[i]):
                if C: X[C.pop()] = i
        assert not C
        for g in rest: X[g] = o
        return X
    def hitting(pairs):
        H = []
        for P in pairs:
            if not (P & set(H)):
                common = [g for g in P if any(g in Q for Q in pairs if Q is not P)]
                H.append(min(common) if common else min(P))
        return H
    NA, F, cap = state(Y, U, J)
    omega = len(J) - sum(cap)
    if omega <= 0: return complete(Y, U, J, cap, None, sorted(J)), 'c2'
    r = next(i for i in reversed(order) if i not in U)
    assert r not in F
    E = exposed(r, Y, U, J)
    pairs = [{b[x], c[x]} & J for x in E]
    H = hitting(pairs)
    if len(H) <= sum(cap) - cap[r]:
        return complete(Y, U, J, cap, r, H), 'owner_r'
    # the bad case: k = leader of the last block, a need chain from k to r (first needer each time)
    k = order[max(t for t in range(n) if ins[t])]
    assert k in E and k in F and k != r
    chain = [k]
    while chain[-1] != r:
        x = chain[-1]
        nxt = next(j for j in order[order.index(x) + 1:] if j not in U and Y[x] in needs(j, Y))
        chain.append(nxt)
    Y2 = list(Y)
    for t in range(len(chain) - 1, 0, -1): Y2[chain[t]] = Y[chain[t - 1]]
    Y2[k] = b[k]; U2 = U | {k}
    J2 = (J | ({Y[r]} if Y[r] is not None else set())) - {b[k], c[k]}
    NA2, F2, cap2 = state(Y2, U2, J2)
    assert NA2 <= NA
    omega2 = len(J2) - sum(cap2)
    if omega2 <= 0: return complete(Y2, U2, J2, cap2, None, sorted(J2)), 'rot_c2'
    E2 = exposed(k, Y2, U2, J2)
    assert set(E2) <= set(E) - {k} and all({b[x], c[x]} != {b[k], c[k]} for x in E2)
    H2 = hitting([{b[x], c[x]} & J2 for x in E2])
    assert len(H2) <= sum(cap2)
    return complete(Y2, U2, J2, cap2, k, H2), 'rot_owner_k'

if __name__ == '__main__':
    args, opts = options(sys.argv[1:])
    n = args[0]; ms = args[1:] or list(range(3, 2 * n + 1)); mode = int(opts.get('mode', 0))
    for m in ms:
        tally = collections.Counter()
        for _, sets in gen_cores_nauty(n, m):
            for prof in itertools.product(range(6), repeat=n):
                trip = [tuple(S[p] for p in PERMS[k]) for S, k in zip(sets, prof)]
                it = [lb_run(n, m, trip)] if mode == 0 else runs_all(n, m, trip)
                for Y, order, ins in it:
                    X, tag = lbplus(n, m, trip, Y, order, ins)
                    tally['runs'] += 1; tally[tag] += 1
                    if not raw_ok(n, m, trip, X): tally['FAIL'] += 1; print("FAIL", sets, prof, Y, order, X)
        tally['rotated'] = tally['rot_c2'] + tally['rot_owner_k']
        print(f"n={n} m={m} mode={mode}: " + ", ".join(f"{k} {tally[k]}" for k in
              ('runs', 'c2', 'owner_r', 'rotated', 'rot_c2', 'rot_owner_k', 'FAIL')), flush=True)
