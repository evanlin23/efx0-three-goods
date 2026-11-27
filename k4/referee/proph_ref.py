#!/usr/bin/env python3
"""Referee check of Proposition H (kgen/n3.md §10, branch claude/kgen-n3 at eb95583). Own code, raw EFX0.

For random three-agent instances I (values 0..9, zeros and ties allowed, m <= 6), build the lifted instance: values
scaled by Q = 100, goods t_1, t_2, t_3 added, v_i(t_i) = L + delta, v_i(t_j) = L (L = Q * max_i v_i(M) + 1,
delta = 1). Enumerate every allocation of the lifted instance and, at every EFX0 one, check:
  (1) every agent holds exactly one t;
  (2) the restriction S to M is EFX0 for I up to delta (as the proof derives), hence exactly EFX0 here, since the
      original differences are multiples of Q > delta;
  (3) the lifted instance has distinct tops and relevance bound k + 3.
Also: the lifted instance has an EFX0 allocation whenever I has one, and vice versa (by (2) and the Tops Lemma).
"""
import itertools, random, sys, json

def val(v, i, S):
    return sum(v[i][g] for g in S)

def efx0(v, X):
    n = len(X)
    for i in range(n):
        t = val(v, i, X[i])
        for j in range(n):
            if i != j and X[j]:
                tot = val(v, i, X[j])
                if any(tot - v[i][h] > t for h in X[j]):
                    return False
    return True

def run(N, seed, delta=1):
    rng = random.Random(seed)
    c = dict(instances=0, lifted_efx0=0, fail_one_t=0, fail_restriction=0, fail_tops=0, I_has=0, lifted_has=0,
             mismatch_existence=0)
    Q = 100
    for _ in range(N):
        m = rng.randint(1, 6)
        v = [[rng.choice([0, 0, 1, 2, 3, 5, 9]) for _ in range(m)] for _ in range(3)]
        k = max(sum(1 for x in row if x > 0) for row in v)
        L = Q * max(sum(row) for row in v) + 1
        w = [[Q * x for x in v[i]] + [L + (delta if j == i else 0) for j in range(3)] for i in range(3)]
        T = [m, m + 1, m + 2]
        c["instances"] += 1
        tops_ok = all(max(range(m + 3), key=lambda g: w[i][g]) == T[i] and
                      sum(1 for g in range(m + 3) if w[i][g] == w[i][T[i]]) == 1 for i in range(3))
        tops_ok &= max(sum(1 for x in row if x > 0) for row in w) <= k + 3
        if not tops_ok:
            c["fail_tops"] += 1
        I_has = any(efx0(v, [[g for g in range(m) if f[g] == i] for i in range(3)])
                    for f in itertools.product(range(3), repeat=m))
        c["I_has"] += I_has
        lifted_has = False
        for f in itertools.product(range(3), repeat=m + 3):
            X = [[g for g in range(m + 3) if f[g] == i] for i in range(3)]
            if not efx0(w, X):
                continue
            lifted_has = True
            c["lifted_efx0"] += 1
            if any(sum(1 for g in X[i] if g in T) != 1 for i in range(3)):
                c["fail_one_t"] += 1
                continue
            S = [[g for g in X[i] if g < m] for i in range(3)]
            if not efx0(v, S):
                c["fail_restriction"] += 1
        c["lifted_has"] += lifted_has
        if lifted_has != I_has:
            c["mismatch_existence"] += 1
    print(json.dumps(dict(source=f"Proposition H N={N} seed={seed} Q=100 delta={delta}", **c)))

if __name__ == "__main__":
    run(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]) if len(sys.argv) > 3 else 1)
