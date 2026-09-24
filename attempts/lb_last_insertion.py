"""Reproduces attempts/lb-last-insertion-lookahead.md: runs of LB's Phase 1 with arbitrary insertion choices in which
the LAST insertion step inserts an agent of minimal lookahead count (construct.py's count, ties allowed), yet the owner
r of proofs/lb_last_step.md (the last-processed agent that is not upgraded) is not a valid owner. Standalone Python,
written separately from src/lb_tree.c; the R1 key, the lookahead count and Phase 2 follow src/construct.py.
Usage: python attempts/lb_last_insertion.py        (the n = 6, m = 10 example; about 1 s)"""
import itertools

def runs(n, m, trip):
    """Every run of Phase 1 over all insertion choices: yields (picks Y, junk J, order, insertion log), where the
    insertion log lists, per insertion step, (chosen agent, {candidate: lookahead count})."""
    R = [set(t) for t in trip]
    rank = [{g: r for r, g in enumerate(t)} for t in trip]
    def r1_step(A, G, Y, order):
        best = None
        for i in sorted(A):
            left = R[i] & G
            if len(left) <= 2:
                fav = min(left, key=lambda g: rank[i][g]) if left else None
                key = (rank[i][fav] if left else 3, len(left), i)
                if best is None or key < best[0]: best = (key, i, fav)
        if best is None: return False
        _, i, fav = best
        Y[i] = fav; A.discard(i); G.discard(fav); order.append(i)
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
    def rec(A, G, Y, order, log):
        A, G, Y, order = set(A), set(G), list(Y), list(order)
        while A and r1_step(A, G, Y, order): pass
        if not A:
            yield Y, sorted(G), order, log; return
        cnt = {}
        for i in sorted(A):
            A2, G2, Y2, o2 = set(A), set(G), list(Y), []
            Y2[i] = trip[i][0]; A2.discard(i); G2.discard(trip[i][0])
            while A2 and r1_step(A2, G2, Y2, o2): pass
            cnt[i] = na_count(A2, G2, Y2)
        for i in sorted(A):
            Y2 = list(Y); Y2[i] = trip[i][0]
            yield from rec(A - {i}, G - {trip[i][0]}, Y2, order + [i], log + [(i, cnt)])
    yield from rec(set(range(n)), set(range(m)), [None] * n, [], [])

def phase2(n, m, trip, Y, J):
    """construct.py's Phase 2 up to the owner search: upgraded set, NA, frozen, slots, junk."""
    rank = [{g: r for r, g in enumerate(t)} for t in trip]
    held = [rank[k][Y[k]] if Y[k] is not None else 3 for k in range(n)]
    J = set(J); up = []
    needed = lambda: {g for k in range(n) if k not in up for g in trip[k][:held[k]]}
    while True:
        NA = needed()
        k = next((k for k in range(n) if k not in up and held[k] == 1 and trip[k][2] in J and trip[k][1] not in NA), None)
        if k is None: break
        up.append(k); J.discard(trip[k][2])
    NA = needed()
    frozen = [Y[k] is not None and Y[k] in NA for k in range(n)]
    cap = [0 if frozen[k] or k in up else (1 if Y[k] is not None else 2) for k in range(n)]
    return set(up), NA, frozen, cap, sorted(J), held

def valid_owners(n, m, trip, Y, J):
    up, NA, frozen, cap, J, held = phase2(n, m, trip, Y, J)
    if len(J) <= sum(cap): return None, up, frozen
    ok = []
    for o in range(n):
        if frozen[o]: continue
        need = len(J) - (sum(cap) - cap[o])
        L0 = ({Y[o]} if Y[o] is not None else set()) | ({trip[o][2]} if o in up else set())
        if any(not any(k != o and held[k] == 0 and k not in up and trip[k][1] in L and trip[k][2] in L for k in range(n))
               for JL in itertools.combinations(J, need) for L in [L0 | set(JL)]):
            ok.append(o)
    return ok, up, frozen

if __name__ == '__main__':
    PERMS = list(itertools.permutations(range(3)))
    sets = [[0, 1, 5], [0, 4, 6], [1, 4, 7], [2, 4, 8], [3, 4, 9], [2, 3, 4]]
    prof = (0, 0, 1, 1, 2, 1)
    n, m = 6, 10
    trip = [tuple(S[p] for p in PERMS[k]) for S, k in zip(sets, prof)]
    print(f"core {sets}, profile {prof}; (a, b, c) per agent: {trip}")
    shown = 0; total = bad = 0
    for Y, J, order, log in runs(n, m, trip):
        total += 1
        last, cnt = log[-1]
        if cnt[last] != min(cnt.values()): continue
        ok, up, frozen = valid_owners(n, m, trip, Y, J)
        if ok is None: continue
        r = next(i for i in reversed(order) if i not in up)
        if r in ok: continue
        bad += 1
        if shown < 2:
            shown += 1
            print(f"  run: order {order}, insertion steps {[(i, c) for i, c in log]}")
            print(f"       picks {Y}, junk {J}, upgraded {sorted(up)}, frozen {[k for k in range(n) if frozen[k]]}")
            print(f"       last insertion: agent {last}, count {cnt[last]} = minimum; r = {r} is NOT a valid owner; "
                  f"valid owners: {ok}")
    print(f"{total} runs over all insertion choices; {bad} with a count-minimal last insertion and r not a valid owner")
