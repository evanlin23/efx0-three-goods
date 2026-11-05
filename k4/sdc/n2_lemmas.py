"""Machine checks of the two written n = 2 lemmas of k4/sdc.md §20 on random two-agent additive instances (zeros and
ties allowed; favourites and tops by value, ties to the smaller index), raw EFX0 definition.
  DT2: if the tops a (agent 0) and b (agent 1) differ, the construction "agent 0 splits M - {a, b} by the greedy EFX0
       partition for v_0 (decreasing v_0, each good to the part of smaller v_0-value), agent 1 adds its preferred part
       to b, agent 0 gets a plus the other part" is EFX0 and gives each agent its top.
  SW:  for an EFX0 allocation X: (i) if each agent prefers the other's favourite held good to its own, swapping the two
       favourites gives an EFX0 allocation; (ii) if agent i prefers a good g of X_j other than F_j to every good of X_i,
       and h in X_i has v_j(h) >= v_j(g), swapping g and h gives an EFX0 allocation.  (Each raises Phi under strict
       values.)

    python3 k4/sdc/n2_lemmas.py SEED T M"""
import itertools, random, sys, collections


def V(v, S): return sum(v[g] for g in S)


def theta(v, S): return V(v, S) - min(v[g] for g in S) if S else 0


def efx0(val, X): return all(V(val[i], X[i]) >= theta(val[i], X[1 - i]) for i in range(2))


def top(v, S):
    S = [g for g in S if v[g] > 0]
    return max(S, key=lambda g: (v[g], -g)) if S else None


def greedy(v, goods):
    P, Q = [], []
    for g in sorted(goods, key=lambda h: (-v[h], h)):
        (P if V(v, P) <= V(v, Q) else Q).append(g)
    return P, Q


if __name__ == '__main__':
    seed, T, M = map(int, sys.argv[1:4]); rng = random.Random(seed); C = collections.Counter()
    print('$ python3 k4/sdc/n2_lemmas.py', *sys.argv[1:])
    for t in range(T):
        m = rng.randint(2, M)
        val = [[rng.choice([0, 0, 1, 2, 3, 5, 8, 13, rng.randint(1, 40)]) for g in range(m)] for i in range(2)]
        a, b = top(val[0], range(m)), top(val[1], range(m))
        if a is not None and b is not None and a != b:
            P, Q = greedy(val[0], [g for g in range(m) if g not in (a, b)])
            Cpart, Dpart = (P, Q) if V(val[1], P) >= V(val[1], Q) else (Q, P)
            X = [[a] + Dpart, [b] + Cpart]
            C['DT2 instances'] += 1; C['DT2 construction EFX0'] += efx0(val, X)
            if not efx0(val, X): print('DT2 FAILS', val, X, flush=True)
        # random EFX0 allocations for SW
        for trial in range(20):
            asg = [rng.randrange(2) for g in range(m)]
            X = [[g for g in range(m) if asg[g] == i] for i in range(2)]
            if not efx0(val, X) or not X[0] or not X[1]: continue
            F = [top(val[i], X[i]) for i in range(2)]
            if None in F: continue
            if val[0][F[1]] > val[0][F[0]] and val[1][F[0]] > val[1][F[1]]:
                Y = [[g for g in X[0] if g != F[0]] + [F[1]], [g for g in X[1] if g != F[1]] + [F[0]]]
                C['SW(i) cases'] += 1; C['SW(i) EFX0'] += efx0(val, Y)
                if not efx0(val, Y): print('SW(i) FAILS', val, X, flush=True)
            for i in range(2):
                j = 1 - i
                for g in X[j]:
                    if g == F[j] or not all(val[i][g] > val[i][x] for x in X[i]): continue
                    for h in X[i]:
                        if val[j][h] >= val[j][g]:
                            Y = [None, None]; Y[i] = [x for x in X[i] if x != h] + [g]; Y[j] = [x for x in X[j] if x != g] + [h]
                            C['SW(ii) cases'] += 1; C['SW(ii) EFX0'] += efx0(val, Y)
                            if not efx0(val, Y): print('SW(ii) FAILS', val, X, g, h, flush=True)
    for k in sorted(C): print(k, C[k])
