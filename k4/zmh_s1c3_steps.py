#!/usr/bin/env python3
"""The steps of the proof of Proposition S1c₃ (k4/zmove_hall.md §3.2), tested one by one on configurations of random
n = 3 profiles (workstream proof/k4-zmove-hall). EVIDENCE tooling, k4/zmh_lib.py's model.

The proposition itself concerns Z′-maxima of non-completable keys, where (on the data) its hypothesis never holds. So
each step is tested here as the implication it is, on every pool-optimal configuration Q (not only maxima) of every
f = 1 key (g, x) with x big-top and both free agents terminals:
  PK      Lemma PK: o a leaf, y ≠ o with a filler f, ℓ ∈ L ∩ U_x, U_x ⊆ X_o: Q* (y on H_y + ℓ, pool L − ℓ + f) is a
          configuration and o is a valid owner of it (X*_o threatens nobody, x included);
  I2      Case (i), second bullet: both leaves, U_x ⊆ L, no filler, y values ℓ ∈ U_x: ℓ = u₃(y), Q_y = {u₁, u₂}, and
          y on {u₁, u₃} (pool L − u₃ + u₂) makes the other agent a valid owner;
  II-kind Case (ii): y_a threatens y_b, y_b a leaf: y_b is (Tg) and Q_{y_a} = {u₂, u₃} of y_b;
  II-ex   Case (ii), y_a without filler, its fourth good w in L or y_b's filler: the exchange Q′ is a configuration with
          r′(Q′) > r′(Q).
Any failed assertion is printed (it would refute a step).

usage: python3 k4/zmh_s1c3_steps.py K SEED      (K random profiles per n = 3 core)"""
import collections, json, os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zmh_lib import Prof, show, pc, bits
from zmh_s1c import rand_profiles, bigtop
from zmh_classes import pool_optimal


def r_of(pr, key, Q):
    F, NN, U = pr.key_data(key)
    return sum(1 for y, q in Q.items() if pr.val(y, q) >= pr.val(y, U[y] & ~q))


def admissible(pr, y, H, Uy):
    return 0 < pc(H) <= 2 and not (H & ~Uy) and all(pr.v[y][g] < pr.val(y, H) for g in bits(Uy & ~H))


def valid_owner(pr, key, Q, L, o):
    x = next(i for i in range(pr.n) if key[i] is not None)
    X = Q[o] | L
    if pr.threat(x, X, pr.val(x, key[x])): return False
    return not any(pr.threat(w, X, pr.val(w, Q[w])) for w in Q if w != o)


def main(argv):
    from zmh_lib import load_inputs
    src = load_inputs(argv[0]) if not argv[0].isdigit() else \
        rand_profiles('rand:results/k4_certs_3.json.gz:%d:%d' % (int(argv[0]), int(argv[1])))
    cnt = collections.Counter()
    for rec in src:
        if len(rec['sets']) != 3: continue
        pr = Prof(rec['sets'], rec['vals'], rec['m'])
        if pr.f != 1 or pr.omega < 2: continue
        for key in pr.keys:
            x = next(i for i in range(3) if key[i] is not None)
            g = key[x]
            if not bigtop(pr, x, next(bits(g))): continue
            F, NN, U = pr.key_data(key)
            Ux = U[x]
            ys = [i for i in range(3) if i != x]
            for P in pr.config_states(key):
                if not all(pr.needs(y, P[y]) & g for y in ys): continue        # both terminals
                for Q, L in pr.configs_over(P, key):
                    if not pool_optimal(pr, key, Q, L): continue
                    cnt['configurations'] += 1
                    X = {y: Q[y] | L for y in ys}
                    thr = {(a, b): pr.threat(b, X[a], pr.val(b, Q[b])) for a in ys for b in ys if a != b}
                    leaf = {y: not any(thr[(y, b)] for b in ys if b != y) for y in ys}
                    fill = {y: Q[y] & ~pr.R[y] for y in ys}
                    # PK
                    for o in ys:
                        if not leaf[o] or (Ux & ~X[o]): continue
                        for y in ys:
                            if y == o or not fill[y]: continue
                            f = fill[y]
                            for l in bits(L & Ux):
                                lm = 1 << l
                                Q2 = dict(Q); Q2[y] = (Q[y] & ~f) | lm; L2 = (L & ~lm) | f
                                ok = admissible(pr, y, Q2[y] & U[y], U[y]) and valid_owner(pr, key, Q2, L2, o)
                                cnt['PK tested'] += 1
                                if not ok:
                                    cnt['PK FAILS'] += 1; print('PK FAILS', json.dumps(rec), show(P), flush=True)
                    a, b = ys
                    if not thr[(a, b)] and not thr[(b, a)]:
                        # Case (i), second bullet
                        if (Ux & ~L) or fill[a] or fill[b]: continue
                        for y in ys:
                            o = b if y == a else a
                            for l in bits(Ux & pr.R[y]):
                                cnt['I2 tested'] += 1
                                us = sorted(bits(U[y]), key=lambda h: -pr.v[y][h])
                                ok = len(us) == 3 and l == us[2] and Q[y] == (1 << us[0]) | (1 << us[1])
                                if ok:
                                    Q2 = dict(Q); Q2[y] = (1 << us[0]) | (1 << us[2])
                                    L2 = (L & ~(1 << us[2])) | (1 << us[1])
                                    ok = admissible(pr, y, Q2[y], U[y]) and valid_owner(pr, key, Q2, L2, o)
                                if not ok:
                                    cnt['I2 FAILS'] += 1; print('I2 FAILS', json.dumps(rec), show(P), flush=True)
                    else:
                        ya, yb = (a, b) if thr[(a, b)] else (b, a)
                        if thr[(yb, ya)] or not leaf[yb]: continue
                        cnt['II tested'] += 1
                        ub = sorted(bits(U[yb]), key=lambda h: -pr.v[yb][h])
                        kind = len(ub) == 3 and pc(Q[yb] & U[yb]) == 1 and Q[yb] & (1 << ub[0]) and \
                            pr.v[yb][ub[0]] < pr.v[yb][ub[1]] + pr.v[yb][ub[2]] and Q[ya] == (1 << ub[1]) | (1 << ub[2])
                        if not kind:
                            cnt['II-kind FAILS'] += 1; print('II-kind FAILS', json.dumps(rec), show(P), flush=True)
                            continue
                        if fill[ya]: continue
                        ws = list(bits(pr.R[ya] & ~g & ~Q[ya]))
                        if len(ws) != 1: continue
                        w = ws[0]; wm = 1 << w
                        fb = Q[yb] & ~pr.R[yb]
                        if not (wm & L or wm == fb): continue
                        cnt['II-ex tested'] += 1
                        pq = sorted(bits(Q[ya]), key=lambda h: -pr.v[ya][h])
                        Q2 = dict(Q); Q2[ya] = (1 << pq[0]) | wm; Q2[yb] = (1 << ub[0]) | (1 << pq[1])
                        ok = admissible(pr, ya, Q2[ya] & U[ya], U[ya]) and admissible(pr, yb, Q2[yb] & U[yb], U[yb]) \
                            and r_of(pr, key, Q2) > r_of(pr, key, Q)
                        if not ok:
                            cnt['II-ex FAILS'] += 1; print('II-ex FAILS', json.dumps(rec), show(P), flush=True)
    for kk in sorted(cnt): print('%-30s %d' % (kk, cnt[kk]))


if __name__ == '__main__':
    main(sys.argv[1:])
