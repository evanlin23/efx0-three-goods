"""Counterexample to Claim X (attempts/k4-p3-uncoupled-owners.md), replayed by brute force: a (4, 3) core with n = 4,
m = 8 and strict balanced types, Phase 1 bases [1], [5], [3], [4] (index insertion), frozen agents 0 and 1, free agents
2 and 3 whose picks no frozen agent values; no EFX0 allocation keeps the four bases with agents 0 and 1 holding at most
two goods each (brute force over all 4^4 placements of the four junk goods, raw EFX0 definition). Also prints the
one-owner check and whether some EFX0 allocation keeps the bases at all.
    python3 k4/p3/claim_x_cex.py
"""
import itertools
sets = [[0, 1, 2, 6], [1, 2, 5, 7], [3, 4, 5, 6], [3, 4, 7]]
vals = [[3, 10, 6, 8], [8, 4, 6, 3], [7, 6, 10, 2], [2, 4, 3]]
n, m = 4, 8
v = [dict(zip(S, V)) for S, V in zip(sets, vals)]
def efx0(X):
    for i in range(n):
        own = sum(v[i].get(g, 0) for g in X[i])
        for j in range(n):
            if i != j and X[j]:
                w = [v[i].get(g, 0) for g in X[j]]
                if sum(w) - min(w) > own: return False
    return True
base = {1: 0, 5: 1, 3: 2, 4: 3}
junk = [g for g in range(m) if g not in base]
print('valuers per good:', [sum(g in S for S in sets) for g in range(m)], ' junk:', junk)
res = {'owners 2, 3 (agents 0, 1 at most two goods)': False, 'any EFX0 allocation keeping the bases': False}
for asg in itertools.product(range(n), repeat=len(junk)):
    own = dict(base); own.update(zip(junk, asg))
    X = [[g for g in range(m) if own[g] == i] for i in range(n)]
    if efx0(X):
        res['any EFX0 allocation keeping the bases'] = True
        if len(X[0]) <= 2 and len(X[1]) <= 2: res['owners 2, 3 (agents 0, 1 at most two goods)'] = True; print('  found', X)
for k, r in res.items(): print(f'{k}: {r}')
