"""Independent replay (no repository code, raw EFX0 definition, values 10 > 8 > 7) of the counterexample to
Conjecture T'_k of k4/k3_oc1.md §12 (one rotation into a terminal completes with no owner or with owner k), in
attempts/k4-k3oc1-tprime-k.md.

Instance: an n = 7, m = 11 ledger core (results/certs_7_11.json.gz), agents a > b > c:
  0: 7 > 0 > 8   1: 5 > 7 > 9   2: 5 > 10 > 7   3: 0 > 3 > 2   4: 1 > 2 > 6   5: 1 > 6 > 4   6: 3 > 4 > 6
Order (2, 1, 0, 5, 6, 3, 4).  The only terminal is 4 (it holds its c, 6); its exposed agents are 5 and 6, which share
the pair {4, 6}.  The rotations into 4 are the ring 4 -> 5 -> 4 (agent 5 takes {6, 4}, agent 4 receives 1) and the
ring 4 -> 6 -> 3 -> 4 (agent 6 takes {4, 6}, agent 3 receives 3, agent 4 receives 2).  Checks: (1) the picks have no
one-absorber completion; (2) for each rotation, the set of absorbers over all one-absorber completions keeping the
bases: it contains neither 'none' nor k, but contains the terminal 4.
    python3 attempts/k4_k3oc1_tprime_k.py"""
import itertools
SETS = [[7, 0, 8], [5, 7, 9], [5, 10, 7], [0, 3, 2], [1, 2, 6], [1, 6, 4], [3, 4, 6]]
ORDER = (2, 1, 0, 5, 6, 3, 4)
n, m = 7, 11
v = [{s[0]: 10, s[1]: 8, s[2]: 7} for s in SETS]
val = lambda i, S: sum(v[i].get(g, 0) for g in S)

def efx0(X):
    return all(val(i, set(X[j]) - {h}) <= val(i, X[i]) for i in range(n) for j in range(n) if i != j for h in X[j])

def absorbers(X0):
    """every absorber (agent given >= 2 unallocated goods, or 'none') of a one-absorber EFX0 completion"""
    J = [g for g in range(m) if not any(g in b for b in X0)]; out = set()
    for asg in itertools.product(range(n), repeat=len(J)):
        ab = [a for a in range(n) if asg.count(a) >= 2]
        if len(ab) > 1: continue
        X = [list(X0[a]) + [g for g, a2 in zip(J, asg) if a2 == a] for a in range(n)]
        if efx0(X): out.add(ab[0] if ab else 'none')
    return out

taken = set(); Y = [None] * n
for i in ORDER:
    Y[i] = max((g for g in SETS[i] if g not in taken), key=lambda g: v[i][g]); taken.add(Y[i])
picks = [[g] for g in Y]
print('picks', Y, 'unallocated', [g for g in range(m) if g not in taken])
print('(1) absorbers of one-absorber completions of the picks:', absorbers(picks) or 'none exists')
for k, ring in ((5, [4, 5]), (6, [4, 6, 3])):          # ring t -> k -> ... -> t: each receives its predecessor's good
    X = [list(b) for b in picks]
    for i, a in enumerate(ring):
        X[ring[(i + 1) % len(ring)]] = [Y[a]]
    X[k] = [SETS[k][1], SETS[k][2]]
    assert all(val(a, X[a]) > val(a, picks[a]) for a in ring)
    print('(2) rotation of k = %d along %s: bases %s; absorbers %s' % (k, ring, X, sorted(absorbers(X), key=str)))
