"""Reproduces the failures of simpler insertion rules for construction LB (see construction_rules.md). Phase 2 and the
raw EFX0 check are those of src/construct.py; only the choice of the inserted agent in a core state differs:
  index       the unprocessed agent of smallest index
  fewclaims   the agent whose top is the top of the fewest unprocessed agents (then index)
  manyclaims  the agent whose top is the top of the most unprocessed agents (then index)
  na          lookahead: fewest goods needed alone (NA) after the forced R1 steps, ignoring upgrades (then index)
  lb          construct.py's rule: the same count after the upgrades that are already certain
Usage (from the repository root): python attempts/construction_rules.py n m [m ...]
Prints, per rule, the number of failing (core, profile) pairs and the first failing one."""
import sys, os, itertools, collections
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'src'))
import construct
from construct import phase2, raw_ok, PERMS
from cores_nauty import gen_cores_nauty

def phase1(n, m, trip, rule):
    if rule == 'lb': return construct.phase1(n, m, trip)
    R = [set(t) for t in trip]; rank = [{g: r for r, g in enumerate(t)} for t in trip]
    def r1_step(A, G, Y):
        best = None
        for i in sorted(A):
            left = R[i] & G
            if len(left) <= 2:
                fav = min(left, key=lambda g: rank[i][g]) if left else None
                key = (rank[i][fav] if left else 3, len(left), i)
                if best is None or key < best[0]: best = (key, i, fav)
        if best is None: return False
        _, i, fav = best; Y[i] = fav; A.discard(i); G.discard(fav); return True
    A, G, Y = set(range(n)), set(range(m)), [None] * n
    while A:
        if r1_step(A, G, Y): continue
        claims = collections.Counter(trip[i][0] for i in A)
        if rule == 'index': i = min(A)
        elif rule == 'fewclaims': i = min(A, key=lambda i: (claims[trip[i][0]], i))
        elif rule == 'manyclaims': i = min(A, key=lambda i: (-claims[trip[i][0]], i))
        elif rule == 'na':
            def score(i):
                A2, G2, Y2 = set(A), set(G), list(Y)
                Y2[i] = trip[i][0]; A2.discard(i); G2.discard(trip[i][0])
                while A2 and r1_step(A2, G2, Y2): pass
                NA = {g for k in range(n) if k not in A2 for g in trip[k][:rank[k][Y2[k]] if Y2[k] is not None else 3]}
                return (len(NA), i)
            i = min(A, key=score)
        Y[i] = trip[i][0]; A.discard(i); G.discard(trip[i][0])
    return Y, sorted(G)

if __name__ == '__main__':
    n = int(sys.argv[1]); rules = ['index', 'fewclaims', 'manyclaims', 'na', 'lb']
    for m in map(int, sys.argv[2:]):
        fails, first = collections.Counter(), {}
        for pi, sets in gen_cores_nauty(n, m):
            for prof in itertools.product(range(6), repeat=n):
                trip = [tuple(S[p] for p in PERMS[k]) for S, k in zip(sets, prof)]
                for r in rules:
                    Y, J = phase1(n, m, trip, r); res = phase2(n, m, trip, Y, J)
                    if not raw_ok(n, m, trip, res[0] if res else None):
                        fails[r] += 1; first.setdefault(r, (sets, prof, trip, Y, J))
        print(f"n={n} m={m}")
        for r in rules:
            print(f"  {r:10s} fails on {fails[r]:5d} pairs" + (
                "; first: sets %s profile %s (a,b,c) %s picks %s junk %s" % first[r] if r in first else ""))
