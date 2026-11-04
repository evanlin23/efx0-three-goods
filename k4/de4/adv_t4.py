"""Adversarial family against the lower-pair order (k4/de4.md §10.4; ledger K4.DE4V3R.LP). EVIDENCE only.

adv_t3.py's double clash of GM4-B (lower-pair holders 0, 1; agents 3, 2 frozen on their tops; robust pairs of
agents 4, 5 holding the b's of 0 and 1), changed so that Lemma 27 (the top swap) does not apply directly: for each
frozen agent t, with probability 1/2 the good just below its top is not the leftover good j but a good held by agent 4
or 5 (j becomes t's c), and agents 4, 5 may hold three goods. make(rng) returns an instance or None."""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from de4lib import Inst
from dead import strict_ok


def make(rng):
    a_u, a_v, b_u, b_v, c_u, d_u, c_v, d_v, j, e1, e2, e3 = range(12)
    cx = rng.choice([c_u, d_u]); cxp = rng.choice([c_v, d_v])
    xs = {2: rng.choice([b_u, b_v, e1, e2]), 3: rng.choice([b_v, b_u, e1, e2])}
    hard = {2: rng.random() < 0.5, 3: rng.random() < 0.5}
    pool4 = [a_u, a_v, c_v, d_v, j, e2, e3]; pool5 = [a_u, a_v, c_u, d_u, j, e1, e3]
    sets = [[a_u, b_u, c_u, d_u], [a_v, b_v, c_v, d_v],
            sorted({a_v, j, cx, xs[2]}), sorted({a_u, j, cxp, xs[3]}),
            sorted({b_u, e1} | set(rng.sample(pool4, rng.choice([1, 2])))),
            sorted({b_v, e2} | set(rng.sample(pool5, rng.choice([1, 2]))))]
    if any(len(s) != len(set(s)) or len(s) < 3 or len(s) > 4 for s in sets):
        return None
    vals = []
    for i, s in enumerate(sets):
        for _ in range(4000):
            V = rng.sample(range(1, 40), len(s))
            d = dict(zip(s, V))
            if max(V) >= sum(V) - max(V):
                continue
            r = sorted(s, key=lambda g: -d[g])
            if i in (0, 1):
                a, b = (a_u, b_u) if i == 0 else (a_v, b_v)
                c, dd = (c_u, d_u) if i == 0 else (c_v, d_v)
                ok = r[0] == a and r[1] == b and d[b] < d[c] + d[dd] < d[a] and d[c] > d[dd]
            elif i in (2, 3):
                top = a_v if i == 2 else a_u
                ok = r[0] == top and (r[1] == xs[i] and r[2] == j if hard[i] else r[1] == j)
            else:
                ok = sum(d[g] for g in s) > 2 * max(V)
            if ok:
                break
        else:
            return None
        vals.append(V)
    I = Inst(sets, vals, 1 + max(max(s) for s in sets))
    return I if strict_ok(I) else None
