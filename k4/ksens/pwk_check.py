"""Lemma PWk (a) (k4/ksens.md §7): in the clean family PW(f, W, r) with r <= 3, the chain x_1 -> w_1 (x_1 takes two
pool goods, w_1 takes p_1, q_1 is released) followed by the explicit completion of the proof is EFX0 and has one
absorber.  Checked against the raw EFX0 definition for every f <= 6, W <= 5, r in {2, 3}.

    python3 k4/ksens/pwk_check.py"""
import _paths
import fam_ladder


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
    rest = D[2:] + [f]                             # the leftover pool good (r = 3) and the released q_1
    if W >= 2: X[f + 1] += rest                    # w_2 absorbs
    elif f >= 2: X[1] += rest                      # W = 1: x_2 absorbs
    else: X[0] += rest
    return X


if __name__ == '__main__':
    print('$ python3 k4/ksens/pwk_check.py')
    bad = 0; tot = 0
    for f in range(1, 7):
        for W in range(1, 6):
            for r in (2, 3):
                sets, vals, m = fam_ladder.clean(f, W, r); X = construct(f, W, r); tot += 1
                assert sorted(g for b in X for g in b) == list(range(m))
                ok = efx0(sets, vals, X)
                if not ok: bad += 1; print('FAIL', f, W, r, X)
    print('configurations', tot, 'not EFX0', bad)
