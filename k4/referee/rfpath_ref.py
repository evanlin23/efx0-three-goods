#!/usr/bin/env python3
"""Referee check of Lemma RF-PATH (k4/girth.md §7 on claude/k4-girth at 8f7ba8aa) and Lemma RF-ROT (k4/ttc.md §14.7 on
claude/k4-ttc at d451ea0c). Own code (serial dictatorship from the definition). Random instances with strict values
(distinct per agent; ≤ 4 or any number of relevant goods), random orders σ (picks need not be perfect). Checks:
RF-PATH (a) Y' = Y off an ejection path x_1 < ... < x_l in σ-order, u takes Y_{x_1}, x_i takes Y_{x_{i+1}}, x_l takes
a junk good of Y, Y_u, or nothing; (b) every x_i strictly loses, u strictly gains; (c) if x_l receives g, nobody wants
g at Y'; σ_{n-1} is unfrozen at Y'; if Y' has exactly one receiver (unfrozen agent) and x_l receives a good, then
x_l = σ_{n-1}; t = Y_u implies Y' = Y. RF-ROT: the last picker is unfrozen; σ_{n-1} is unfrozen unless σ_n wants its
pick; at a start with exactly one receiver, it is σ_n."""
import json, sys, random
from collections import Counter

def sd(v, order, m):
    free = set(range(m)); Y = {}
    for a in order:
        R = [g for g in free if v[a][g] > 0]
        if R:
            g = max(R, key=lambda g: v[a][g]); Y[a] = g; free.discard(g)
        else:
            Y[a] = None
    return Y

def val(v, a, g):
    return 0 if g is None else v[a][g]

def wants(v, j, g, Y):
    return g is not None and v[j][g] > val(v, j, Y[j])

def unfrozen(v, n, Y, i):
    return not any(j != i and wants(v, j, Y[i], Y) for j in range(n))

def run(N, seed, kmax):
    rng = random.Random(seed); c = Counter()
    for _ in range(N):
        n = rng.randint(2, 7); m = rng.randint(n, n + 5)
        v = [[0] * m for _ in range(n)]
        for a in range(n):
            k = rng.randint(1, min(m, kmax))
            for g, x in zip(rng.sample(range(m), k), rng.sample(range(1, 100), k)):
                v[a][g] = x
        sig = list(range(n)); rng.shuffle(sig)
        Y = sd(v, sig, m); u = sig[-1]
        c["instances"] += 1
        # RF-ROT facts
        c["ROT_last_picker_frozen_FAIL"] += not unfrozen(v, n, Y, u)
        if n >= 2:
            s2 = sig[-2]
            c["ROT_second_last_FAIL"] += (not unfrozen(v, n, Y, s2)) and not wants(v, u, Y[s2], Y)
        rec = [i for i in range(n) if unfrozen(v, n, Y, i)]
        if len(rec) == 1:
            c["one_receiver_starts"] += 1; c["ROT_one_receiver_not_last_FAIL"] += rec[0] != u
        Ru = [g for g in range(m) if v[u][g] > 0]
        if not Ru:
            continue
        t = max(Ru, key=lambda g: v[u][g])
        sig2 = [u] + sig[:-1]; Y2 = sd(v, sig2, m)
        if t == Y[u]:
            c["t_is_Yu"] += 1; c["PATH_t_is_Yu_but_changed_FAIL"] += Y2 != Y; continue
        c["path_cases"] += 1
        holder = {Y[a]: a for a in range(n) if Y[a] is not None}
        # build the predicted path
        if t not in holder:
            c["PATH_t_not_a_pick_FAIL"] += 1; continue
        pos = {a: i for i, a in enumerate(sig)}
        changed = [a for a in range(n) if a != u and Y2[a] != Y[a]]
        path = sorted(changed, key=lambda a: pos[a])
        ok = Y2[u] == t and (path and path[0] == holder[t])
        for i in range(len(path) - 1):
            ok &= Y2[path[i]] == Y[path[i + 1]]
        if path:
            d = path[-1]; g = Y2[d]
            junkY = set(range(m)) - {y for y in Y.values() if y is not None}
            ok &= (g is None) or (g in junkY) or (g == Y[u])
        c["PATH_shape_FAIL"] += not ok
        c[f"path_length_{len(path)}"] += 1
        c["PATH_loss_FAIL"] += any(not val(v, a, Y2[a]) < val(v, a, Y[a]) for a in path)
        c["PATH_u_gain_FAIL"] += not val(v, u, Y2[u]) > val(v, u, Y[u])
        if path and Y2[path[-1]] is not None:
            c["PATH_d_wanted_FAIL"] += not unfrozen(v, n, Y2, path[-1])
            rec2 = [i for i in range(n) if unfrozen(v, n, Y2, i)]
            if len(rec2) == 1:
                c["one_receiver_RF_starts"] += 1; c["PATH_d_not_sigma_n_minus_1_FAIL"] += path[-1] != sig[-2]
        c["PATH_sigma_n_minus_1_frozen_FAIL"] += not unfrozen(v, n, Y2, sig[-2])
    print(json.dumps(dict(source=f"RF-PATH / RF-ROT check N={N} seed={seed} kmax={kmax}", **dict(sorted(c.items())))))

if __name__ == "__main__":
    run(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
