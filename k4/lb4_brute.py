"""Brute force: every EFX0 allocation of a small instance (raw definition, explicit integers), and which have at
most one bundle of more than 2 goods.  Usage: lb4_brute.py 'SETS' 'VALS'  (JSON lists, as printed by lb4.c)."""
import itertools, json, sys

def efx0(sets, vals, own, n, m):
    v = [dict(zip(S, V)) for S, V in zip(sets, vals)]
    B = [[g for g in range(m) if own[g] == i] for i in range(n)]
    for i in range(n):
        mine = sum(v[i].get(g, 0) for g in B[i])
        for j in range(n):
            if j != i and B[j] and mine < sum(v[i].get(g, 0) for g in B[j]) - min(v[i].get(g, 0) for g in B[j]):
                return False
    return True

def all_efx0(sets, vals):
    n, m = len(sets), 1 + max(max(S) for S in sets)
    for own in itertools.product(range(n), repeat=m):
        if efx0(sets, vals, own, n, m):
            yield [[g for g in range(m) if own[g] == i] for i in range(n)]

if __name__ == '__main__':
    sets, vals = json.loads(sys.argv[1]), json.loads(sys.argv[2])
    sols = list(all_efx0(sets, vals))
    d2 = [X for X in sols if sum(len(B) > 2 for B in X) <= 1]
    print(f"{len(sols)} EFX0 allocations, {len(d2)} with at most one bundle of > 2 goods")
    for X in d2[:int(sys.argv[3]) if len(sys.argv) > 3 else 20]: print('  ', X)
