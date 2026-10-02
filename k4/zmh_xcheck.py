#!/usr/bin/env python3
"""Second implementation of the ZMOVE verdicts (workstream proof/k4-zmove-hall). EVIDENCE tooling.

The deficits, min-frozen states and move kinds are main's repo-free k4/rt4_n5_indep.py (the PR #86 auditor's code:
its own 𝒫, raw removal-only deficit by enumeration of C, and its T3 / T3⁺ / T4 classification). The configurations are
enumerated here directly from k4/c4min.md §1 (pairs Q_y ⊆ M ∖ 𝒩, Q_y ∩ U_y admissible, the pool the rest), with
(r′, Λ′) of k4/sx.md §2 (ℓ_y over the subsets of R_y), not through the states as k4/zmh_lib.py does. Then per key with
def* > 0: the Z′-maxima, their states P_Q, and whether some P_Q has a T3⁺ move (|Y| <= 1, each helper giving up a good)
to a min-frozen state with deficit <= 0, or the key a T4 edge to a smaller def*. Compared with k4/zmh_lib.py
key by key (def*, the set of P_Q, the number of good moves per P_Q, the verdict).

usage: python3 k4/zmh_xcheck.py [--max=N] [--every=E] [--maxn=N] INPUT ...   (--every counts within each input)"""
import collections, itertools, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import rt4_n5_indep as RI
from zmh_lib import Prof, load_inputs


def zmove_indep(sets, vals, m, all_keys=False, want_ns=False):
    ns = RI.analyse(sets, vals, m)
    n, mf, D, info, classify, f, sigma = (ns[k] for k in ('n', 'mf', 'D', 'info', 'classify', 'f', 'sigma'))
    omega = f - sigma
    if omega < 1: return omega, {}
    v = [dict(zip(S, V)) for S, V in zip(sets, vals)]
    R = [frozenset(S) for S in sets]

    def val(i, X): return sum(v[i].get(g, 0) for g in X)

    def key(X):
        N, NA, J, fz = info(X)
        return tuple(X[i] if fz[i] else None for i in range(n))
    K = collections.defaultdict(list)
    for X in mf: K[key(X)].append(X)
    dstar = {k: min(D[X] for X in Xs) for k, Xs in K.items()}
    lev = {}

    def level(i, S):
        s = val(i, S)
        return sum(1 for r in range(len(sets[i]) + 1) for T in itertools.combinations(sets[i], r) if val(i, T) < s)
    out = {}
    for k, ds in dstar.items():
        if ds <= 0 and not all_keys: continue
        NN = frozenset().union(*[b for b in k if b is not None])
        free = [i for i in range(n) if k[i] is None]
        Mp = sorted(set(range(m)) - NN)
        U = {y: R[y] - NN for y in free}

        def adm(y, A):
            # admissible (k4/c4min.md §1): A ⊆ U_y, |A| <= 2, every good of U_y outside A worth less than A; so A = ∅
            # is admissible exactly when U_y = ∅
            if len(A) > 2 or not A <= U[y]: return False
            return all(v[y][g] < val(y, A) for g in U[y] - A)
        # all configurations: assign pairs to the free agents in turn
        best = None; bestPQ = set()

        def rec(t, used, Hs):
            nonlocal best, bestPQ
            if t == len(free):
                r = sum(1 for y in free if val(y, Hs[y]) >= val(y, U[y] - Hs[y]))
                lam = sum(level(y, Hs[y]) for y in free)
                pot = (r, lam)
                PQ = tuple(k[i] if k[i] is not None else Hs[i] for i in range(n))
                if best is None or pot > best: best, bestPQ = pot, {PQ}
                elif pot == best: bestPQ.add(PQ)
                return
            y = free[t]
            avail = [g for g in Mp if g not in used]
            for pr in itertools.combinations(avail, 2):
                Qy = frozenset(pr)
                H = Qy & U[y]
                if not adm(y, H): continue
                Hs[y] = H
                rec(t + 1, used | Qy, Hs)
            Hs.pop(y, None)
        rec(0, frozenset(), {})
        good = [X for X in mf if D[X] <= 0]
        per = {}
        for PQ in bestPQ:
            assert PQ in D, 'P_Q not min-frozen'
            per[PQ] = sum(1 for X in good if 'T3+' in classify(PQ, X)[0])
        t4 = any('T4' in classify(P, X)[0] for P in K[k] for X in mf if key(X) != k and dstar[key(X)] < ds)
        out[k] = (ds, best, per, t4)
    if want_ns: return omega, out, ns, dstar
    return omega, out


def main(argv):
    opts = {}; ins = []
    for a in argv:
        if a.startswith('--'):
            kk, _, vv = a[2:].partition('='); opts[kk] = vv
        else: ins.append(a)
    mx = int(opts.get('max', 10 ** 9)); every = int(opts.get('every', 1)); maxn = int(opts.get('maxn', 99))
    cnt = collections.Counter()
    for path in ins:
        idx = 0                                   # --every counts within each input
        for rec in load_inputs(path):
            idx += 1
            if (idx - 1) % every or len(rec['sets']) > maxn: continue
            if cnt['profiles'] >= mx: break
            cnt['profiles'] += 1
            sets, vals, m = rec['sets'], rec['vals'], rec.get('m') or 1 + max(max(S) for S in rec['sets'])
            omega, out = zmove_indep(sets, vals, m)
            pr = Prof(sets, vals, m)
            mine = {}
            if pr.omega >= 1:
                for k, ds in pr.dstar.items():
                    if ds <= 0: continue
                    res, t4, best = pr.zmove(k)
                    mine[k] = (ds, best, {P: len(mv) for P, mv in res}, bool(t4))
            conv = lambda P: None if P is None else frozenset(RI_bits(P))
            mine2 = {tuple(conv(b) for b in k): (ds, best, {tuple(frozenset(RI_bits(B)) for B in P): c
                                                            for P, c in per.items()}, t4)
                     for k, (ds, best, per, t4) in mine.items()}
            if mine2 != out:
                cnt['MISMATCH'] += 1
                print('MISMATCH', json.dumps(rec), mine2, out, flush=True)
            for k, (ds, best, per, t4) in out.items():
                cnt['keys def*>0'] += 1
                cnt['Z-maxima'] += len(per)
                cnt['Z-maxima with a move'] += sum(1 for c in per.values() if c)
                if any(per.values()) or t4: cnt['ZMOVE holds'] += 1
                else:
                    cnt['ZMOVE FAILS'] += 1
                    print('ZMOVE FAILS (indep)', json.dumps(rec), k, flush=True)
    for kk in sorted(cnt): print('%-30s %d' % (kk, cnt[kk]))


def RI_bits(b):
    g = 0
    while b:
        if b & 1: yield g
        b >>= 1; g += 1


if __name__ == '__main__':
    main(sys.argv[1:])
