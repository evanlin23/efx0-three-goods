"""Counterexamples to Claims X and X' (attempts/k4-p3-uncoupled-owners.md), replayed by brute force: a (4, 3) core with n = 4,
m = 8 and strict balanced types, Phase 1 bases [1], [5], [3], [4] (index insertion), frozen agents 0 and 1, free agents
2 and 3 whose picks no frozen agent values; no EFX0 allocation keeps the four bases with agents 0 and 1 holding at most
two goods each (brute force over all 4^4 placements of the four junk goods, raw EFX0 definition). Also prints the
one-owner check and whether some EFX0 allocation keeps the bases at all.
    python3 k4/p3/claim_x_cex.py X      Claim X (n = 4, m = 8)
    python3 k4/p3/claim_x_cex.py "X'"   Claim X' (n = 4, m = 9: owners' picks invisible to everyone)
"""
import itertools
import sys
CASES = {'X': ([[0, 1, 2, 6], [1, 2, 5, 7], [3, 4, 5, 6], [3, 4, 7]], [[3, 10, 6, 8], [8, 4, 6, 3], [7, 6, 10, 2], [2, 4, 3]],
               8, {1: 0, 5: 1, 3: 2, 4: 3}, (2, 3)),
         "X'": ([[0, 2, 6, 7], [1, 4, 7, 8], [3, 5, 8], [5, 6, 7, 8]], [[2, 8, 7, 4], [6, 5, 4, 8], [2, 3, 4], [10, 7, 4, 2]],
                9, {2: 0, 8: 1, 3: 2, 5: 3}, (0, 2))}
case = sys.argv[1] if len(sys.argv) > 1 else 'X'
sets, vals, m, base, owners = CASES[case]
n = 4
v = [dict(zip(S, V)) for S, V in zip(sets, vals)]
def efx0(X):
    for i in range(n):
        own = sum(v[i].get(g, 0) for g in X[i])
        for j in range(n):
            if i != j and X[j]:
                w = [v[i].get(g, 0) for g in X[j]]
                if sum(w) - min(w) > own: return False
    return True
junk = [g for g in range(m) if g not in base]
print('valuers per good:', [sum(g in S for S in sets) for g in range(m)], ' junk:', junk)
key = f'owners {owners} (the other agents at most two goods)'
res = {key: False, 'any EFX0 allocation keeping the bases': False}
for asg in itertools.product(range(n), repeat=len(junk)):
    own = dict(base); own.update(zip(junk, asg))
    X = [[g for g in range(m) if own[g] == i] for i in range(n)]
    if efx0(X):
        res['any EFX0 allocation keeping the bases'] = True
        if all(len(X[i]) <= 2 for i in range(n) if i not in owners): res[key] = True; print('  found', X)
for k, r in res.items(): print(f'{k}: {r}')
