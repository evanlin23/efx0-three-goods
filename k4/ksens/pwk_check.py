"""Lemma PWk (a) (k4/ksens.md §7): for PW(f, W, r) with r <= 3, the chain x_1 -> w_1 (x_1 takes two pool goods, w_1
takes p_1, q_1 is released) followed by the explicit completion of the proof is EFX0 with at most one absorber.
Checked against the raw EFX0 definition:
  - clean values (fam_ladder.clean), every f <= 6, W <= 5, r in {2, 3};
  - random values of the whole family (x_j: pick worth P, pool goods each worth less than P and every pair more; wanters:
    every pick above q, the same ranking p_1 > ... > p_f, nothing else), T draws per (f, W, r);
  - W = 0: the picks themselves have a one-absorber completion (SAT, ocsat), clean and random values.
The completion (after the referee's fix, k4/referee/ksens.md §5 on claude/k4-referee): x_1 {d_1, d_2}, w_1 {p_1},
x_j {p_j}, w_i {q_i}; the leftover d_3 (r = 3) and q_1 go
  W >= 2: both to w_2 (the absorber);
  W = 1, f >= 2: q_1 to x_2 and d_3 to w_1 (no absorber);
  W = 1, f = 1: both to x_1.

    python3 k4/ksens/pwk_check.py [T]"""
import sys, random
import _paths
import fam_ladder, ocsat


def efx0(sets, vals, X):
    v = [dict(zip(s, vv)) for s, vv in zip(sets, vals)]; n = len(X)
    for i in range(n):
        own = sum(v[i].get(g, 0) for g in X[i])
        for j in range(n):
            if j == i: continue
            for h in X[j]:
                if sum(v[i].get(g, 0) for g in X[j] if g != h) > own: return False
    return True


def construct(f, W, r):
    """agents 0..f-1 = x_j (p_j = j), f..f+W-1 = w_i (q_i = f + i), pool goods f + W .. f + W + r - 1"""
    D = list(range(f + W, f + W + r)); X = [[j] for j in range(f)] + [[f + i] for i in range(W)]
    X[0] = D[:2]; X[f] = [0]                       # x_1 takes a pair, w_1 takes p_1
    d3 = D[2:]; q1 = [f]
    if W >= 2: X[f + 1] += d3 + q1                 # w_2 absorbs both
    elif f >= 2: X[1] += q1; X[f] += d3            # W = 1: q_1 to x_2, d_3 to w_1
    else: X[0] += d3 + q1
    return X


def random_family(f, W, r, rng):
    D = list(range(f + W, f + W + r)); P_ = list(range(f)); sets, vals = [], []
    for j in range(f):
        P = rng.randint(20, 60)
        while True:
            pool = rng.sample(range(P // 2 + 1, P), r)
            if all(a + b > P for a in pool for b in pool if a != b): break
        sets.append([j] + D); vals.append([P] + pool)
    for i in range(W):
        q = rng.randint(1, 30); pv = sorted(rng.sample(range(q + 1, q + 60), f), reverse=True)   # p_1 > ... > p_f > q
        sets.append(P_ + [f + i]); vals.append(pv + [q])
    return sets, vals, f + W + r


if __name__ == '__main__':
    T = int(sys.argv[1]) if len(sys.argv) > 1 else 200; rng = random.Random(1)
    print('$ python3 k4/ksens/pwk_check.py', T)
    tot = bad = 0
    for f in range(1, 7):
        for W in range(1, 6):
            for r in (2, 3):
                sets, vals, m = fam_ladder.clean(f, W, r); X = construct(f, W, r); tot += 1
                assert sorted(g for b in X for g in b) == list(range(m))
                if not efx0(sets, vals, X): bad += 1; print('FAIL clean', f, W, r, X)
    print('clean values: configurations', tot, 'not EFX0', bad)
    tot = bad = 0
    for f in range(1, 6):
        for W in range(1, 5):
            for r in (2, 3):
                for t in range(T):
                    sets, vals, m = random_family(f, W, r, rng); X = construct(f, W, r); tot += 1
                    if not efx0(sets, vals, X):
                        bad += 1
                        if bad <= 3: print('FAIL random', f, W, r, vals, X)
    print('random values of the family: instances', tot, 'not EFX0', bad)
    # the referee's counterexample to the earlier W = 1 completion: f = 2, W = 1, r = 3, wanter values (12, 8, 5)
    sets, vals, m = random_family(2, 1, 3, rng); vals[2] = [12, 8, 5]
    old = [[3, 4], [1, 5, 2], [0]]                                    # the earlier completion: x_2 absorbs d_3 and q_1
    print('referee instance', vals, ': earlier completion EFX0', efx0(sets, vals, old), '; fixed completion EFX0',
          efx0(sets, vals, construct(2, 1, 3)))
    tot = bad = 0
    for f in range(1, 6):
        for r in (0, 1, 2, 3):
            for t in range(max(1, T // 10)):
                if t == 0: sets, vals, m = fam_ladder.clean(f, 0, r) if r else ([[j] for j in range(f)], [[20]] * f, f)
                else:
                    if r == 0: continue
                    sets, vals, m = random_family(f, 0, r, rng)
                O = ocsat.OC(sets, vals, m); b = ocsat.bases_of(ocsat.sd(sets, vals, tuple(range(f)), m), f); tot += 1
                if not O.holds(b, chain='none', A=1): bad += 1; print('FAIL W=0', f, r, vals)
                O.close()
    print('W = 0 (no wanters): starts', tot, 'without a one-absorber completion of the picks', bad)
