"""Replay for attempts/k4-vm-lp-rs-dual.md, from the definitions only (no repository code; no rklib).

Instance (a random strict connected k = 4 core, cores:4:3000:301 #2548 of k4/vm/data.py): n = 4, m = 6.
Checks, by brute force:
  1. Y = (4, 2, 5, 3) is a maximum matching of minimum rank sum (rank_i(g) = 1 + #{h in R_i : v_i(h) > v_i(g)}).
  2. Its least RS dual prices beta (beta_g >= 0, beta(junk) = 0, beta_g >= beta_{Y_i} - (rank_i(g) - rank_i(Y_i)) on
     every relevant edge) exist, and no frozen agent values the junk above its pick: no agent is dangerous in any of
     the senses tested, so every dual slack condition holds vacuously.
  3. Yet the picks have NO one-absorber EFX0 completion (every assignment of the junk with at most one agent getting
     two or more junk goods violates EFX0): the candidate "dual slack => the picks complete" fails.
  4. One official move repairs it: the ring 0 -> 1 -> 2 -> 0 with junk gives ({0, 2}, {1, 5}, {4}, {3}), EFX0.
    python3 attempts/k4_vm_lp_rs_dual.py"""
import itertools

sets = [[0, 2, 3, 4], [1, 2, 3, 5], [2, 4, 5], [3, 4, 5]]
vals = [[4, 6, 3, 8], [6, 7, 10, 2], [3, 4, 2], [4, 3, 2]]
n, m = 4, 6
v = [dict(zip(S, W)) for S, W in zip(sets, vals)]
val = lambda i, B: sum(v[i].get(g, 0) for g in B)
rank = lambda i, g: 1 + sum(1 for h in v[i] if v[i][h] > v[i][g])


def efx0(X):
    return all(val(i, [h for h in X[j] if h != g]) <= val(i, X[i]) for i in range(n) for j in range(n) if i != j
               for g in X[j])


# 1. maximum matchings and the rank-sum optimum
Ms = [M for M in itertools.product(*[S for S in sets]) if len(set(M)) == n]
assert Ms, 'no perfect agent matching'
best = min(sum(rank(i, M[i]) for i in range(n)) for M in Ms)
Y = (4, 2, 5, 3)
assert Y in Ms and sum(rank(i, Y[i]) for i in range(n)) == best
print('max matchings (all agents matched):', len(Ms), '; least rank sum', best, '; Y =', Y, 'attains it')

# 2. least dual prices and the danger notions
junk = [g for g in range(m) if g not in Y]
beta = {g: 0 for g in range(m)}
for _ in range(10):
    for i in range(n):
        for g in sets[i]:
            if g != Y[i] and g in Y:
                beta[g] = max(beta[g], beta[Y[i]] - (rank(i, g) - rank(i, Y[i])))
assert all(beta[Y[i]] - (rank(i, g) - rank(i, Y[i])) <= 0 for i in range(n) for g in sets[i] if g in junk)
p = [v[i][Y[i]] for i in range(n)]
frozen = [j for j in range(n) if any(i != j and v[i].get(Y[j], 0) > p[i] for i in range(n))]
dangerous = [x for x in frozen if val(x, junk) > p[x]]
print('junk', junk, '; beta', beta, '; frozen', frozen, '; frozen agents valuing the junk above their pick:', dangerous)
assert dangerous == []

# 3. no one-absorber completion at the picks
found = None
for f in itertools.product(range(n), repeat=len(junk)):
    if sum(1 for a in range(n) if f.count(a) >= 2) > 1: continue
    X = [[Y[i]] for i in range(n)]
    for g, a in zip(junk, f): X[a].append(g)
    if efx0(X): found = X; break
assert found is None
print('no one-absorber EFX0 completion of the picks: the dual-slack certificate fails here')

# 4. the repairing ring
X = [[0, 2], [1, 5], [4], [3]]
assert efx0(X) and sorted(g for b in X for g in b) == list(range(m))
assert val(0, [0, 2]) > p[0] and val(1, [1, 5]) > p[1] and val(2, [4]) > p[2]
print('one ring repairs it:', X)
