"""Independent replay (no repository code, raw EFX0 definition, explicit values) of the counterexample to the
"every k" forms -- kgen-n3's T1-E and k4/k3_oc1.md's Conjecture T-E -- in attempts/k4-k3oc1-every-k.md.

Instance (k = 3; n = 7 ledger core from results/certs_7_12.json.gz; values a, b, c = 10, 8, 7 for every agent; any
strictly balanced values give the same comparisons of subset sums):
  agent 0: 3 > 9 > 0   agent 1: 4 > 6 > 10   agent 2: 5 > 11 > 8   agent 3: 2 > 0 > 8
  agent 4: 3 > 2 > 1   agent 5: 5 > 1 > 7    agent 6: 7 > 4 > 6
Order 0, 1, ..., 6.  Checks: (1) the picks have no one-absorber completion; (2) after the rotation of k = 1 into the
only terminal 6 (agent 1 takes its pair {6, 10}, agent 6 receives 1's top 4; the only chain from 1, since agent 6 is
the only other agent valuing good 4) no one-absorber completion exists; (3) the rotations of k = 0, 2, 3 along their
earliest-wanter chains into 6 each have one.
    python3 attempts/k4_k3oc1_every_k.py"""
import itertools
SETS = [[3, 9, 0], [4, 6, 10], [5, 11, 8], [2, 0, 8], [3, 2, 1], [5, 1, 7], [7, 4, 6]]
n, m = 7, 12
v = [{s[0]: 10, s[1]: 8, s[2]: 7} for s in SETS]
val = lambda i, S: sum(v[i].get(g, 0) for g in S)

def efx0(X):
    return all(val(i, set(X[j]) - {h}) <= val(i, X[i]) for i in range(n) for j in range(n) if i != j for h in X[j])

def completion(bundles):
    """some one-absorber EFX0 completion of the partial allocation (every unallocated good given out)"""
    J = [g for g in range(m) if not any(g in b for b in bundles)]
    for asg in itertools.product(range(n), repeat=len(J)):
        if sum(1 for a in range(n) if asg.count(a) >= 2) > 1: continue
        X = [list(bundles[a]) + [g for g, a2 in zip(J, asg) if a2 == a] for a in range(n)]
        if efx0(X): return X
    return None

taken = set(); Y = [None] * n
for i in range(n):
    av = [g for g in SETS[i] if g not in taken]
    Y[i] = max(av, key=lambda g: v[i][g]); taken.add(Y[i])
picks = [[g] for g in Y]
print('picks', Y, 'unallocated', [g for g in range(m) if g not in taken])
print('(1) one-absorber completion of the picks:', completion(picks))

def rotate(chain):
    """chain k = x0, x1, ..., xs = t: x_i receives x_{i-1}'s good, k takes its pair (from the junk and t's good)"""
    X = [list(b) for b in picks]; k = chain[0]
    for i in range(len(chain) - 1, 0, -1): X[chain[i]] = [Y[chain[i - 1]]]
    X[k] = [SETS[k][1], SETS[k][2]]
    for a in range(n):
        if a != k: X[a] = [g for g in X[a] if g not in X[k]]
    for a in chain[1:]: assert val(a, X[a]) > val(a, picks[a]), 'not improving'
    assert val(k, X[k]) > val(k, picks[k])
    return X
for chain in ([1, 6], [0, 4, 5, 6], [2, 5, 6], [3, 4, 5, 6]):
    X = rotate(chain)
    print('(%s) rotation %s -> %s; one-absorber completion: %s' % ('2' if chain[0] == 1 else '3', chain, X, completion(X)))
