"""Obstructions to the multigraph proof's structure once a good has three valuers (proofs/multigraph_extension.md, section 5).
Brute force over every allocation, with the raw EFX0 definition under three strictly balanced realizations (no use of L5).

"Height one" (the shape of the multigraph proof's allocations, digest section 2): no agent both envies someone and is envied,
where i envies j if v_i(X_j) > v_i(X_i). Envy between bundles is decided by the same subset-sum order as EFX0 (L5(i)); the
script checks that the three realizations agree.

For every connected core with n = 3 (all m) and every ranking profile it reports whether a popular matching exists and
whether some EFX0 allocation has height one. Then it checks the two configurations of section 5 in detail:
  O1: core H3 [[0,1,2],[0,1,3],[0,1,4]], profile (0,0,0): no popular matching; its EFX0 allocations are exactly the six
      assignments of {0}, {1}, {2,3,4}, and each has an agent that envies and is envied.
  O2: core [[0,1,3],[0,2,3],[1,2,3]], rankings (0,1,3), (0,2,3), (3,1,2): one good (3) with three valuers; a popular matching
      exists, and all four EFX0 allocations have an agent that envies and is envied.
Usage: mgx_obstructions.py   (exit status 1 if a claim fails)"""
import itertools, sys
from cores_nauty import gen_cores_nauty
from mgx import popular_matching
PERMS = list(itertools.permutations(range(3)))
VALS = ((4, 3, 2), (10, 9, 2), (10, 6, 5))

def efx0_allocations(n, m, trip):
    """[(X, height_one)] for every EFX0 allocation X (X[g] = owner)."""
    out = []
    for X in itertools.product(range(n), repeat=m):
        B = [[g for g in range(m) if X[g] == j] for j in range(n)]
        verdicts = set()
        for vals in VALS:
            v = [dict(zip(t, vals)) for t in trip]
            ok, env = True, set()
            for i in range(n):
                own = sum(v[i].get(g, 0) for g in B[i])
                for j in range(n):
                    if j != i and B[j]:
                        w = [v[i].get(g, 0) for g in B[j]]
                        if sum(w) - min(w) > own: ok = False
                        if sum(w) > own: env.add((i, j))
            h1 = not ({i for i, _ in env} & {j for _, j in env})
            verdicts.add((ok, h1 if ok else None))
        assert len(verdicts) == 1, f'realizations disagree: {trip} {X}'
        ok, h1 = verdicts.pop()
        if ok: out.append((X, h1))
    return out

def main():
    fails = []
    print('n = 3, every connected core and every profile (6^3 = 216 per core):')
    for m in range(3, 7):
        for pi, sets in gen_cores_nauty(3, m):
            deg = {g: sum(g in S for S in sets) for S in sets for g in S}
            many = sorted(g for g, d in deg.items() if d >= 3)
            nopm = noh1 = noh1_pm = 0; ex = None
            for prof in itertools.product(range(6), repeat=3):
                trip = [tuple(S[p] for p in PERMS[k]) for S, k in zip(sets, prof)]
                pm = popular_matching(3, trip) is not None
                al = efx0_allocations(3, m, trip)
                if not al: fails.append(('no EFX0 allocation', sets, trip))
                nopm += not pm
                if not any(h for _, h in al):
                    noh1 += 1; noh1_pm += pm
                    if ex is None: ex = trip
            print(f'  m = {m} {sets}: goods with >= 3 valuers {many}; profiles without a popular matching {nopm}; '
                  f'profiles with no height-one EFX0 allocation {noh1} (with a popular matching {noh1_pm})'
                  + (f'; e.g. {ex}' if ex else ''))
            if not many and (nopm or noh1): fails.append(('multigraph core fails', sets))

    trip = [(0, 1, 2), (0, 1, 3), (0, 1, 4)]
    al = efx0_allocations(3, 5, trip)
    shapes = {tuple(sorted(tuple(g for g in range(5) if X[g] == j) for j in range(3))) for X, _ in al}
    o1 = (popular_matching(3, trip) is None and shapes == {((0,), (1,), (2, 3, 4))} and len(al) == 6
          and not any(h for _, h in al))
    print(f'O1 H3 {trip}: popular matching: {popular_matching(3, trip)}; EFX0 allocations {len(al)}, bundle shapes '
          f'{sorted(shapes)}; height one: {sum(h for _, h in al)} -> {"OK" if o1 else "FAIL"}')

    trip = [(0, 1, 3), (0, 2, 3), (3, 1, 2)]
    al = efx0_allocations(3, 4, trip)
    Y = popular_matching(3, trip)
    o2 = Y is not None and len(al) == 4 and not any(h for _, h in al)
    print(f'O2 {trip}: popular matching {Y}; EFX0 allocations (owner of goods 0..3): {[X for X, _ in al]}; '
          f'height one: {sum(h for _, h in al)} -> {"OK" if o2 else "FAIL"}')
    if not (o1 and o2): fails.append('O1/O2')
    print('FAILURES:', fails if fails else 'none')
    sys.exit(1 if fails else 0)

if __name__ == '__main__':
    main()
