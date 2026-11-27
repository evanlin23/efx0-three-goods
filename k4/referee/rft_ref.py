#!/usr/bin/env python3
"""Referee check of girth's Lemma ORD and Lemma RF-T-A (k4/girth.md §7 on claude/k4-girth at 56941dc6, draft PR #161),
with Lemma RF-T's reduction re-tested. Own code (c13_ref.py, cert_ref.py, leanrf_ref.py); nothing from k4/girth/ is run.

Counterfactual sample as in girth.md ("The right target"), rebuilt independently: P random strict balanced profiles per
pure n = 5 core with m = 8 (656 cores, from results/k4_certs_5_pure.json.gz), every order sigma with perfect picks Y,
every receiver u of Y; Y' = SD(u, sigma - u) perfect with one receiver d and D_T' empty; RF path u = x0, ..., x_l = d
with l >= 2 and d taking a junk good g of Y; a valid trade: p pick-dangerous at Y' keeping Y_p, j in J cap R_p,
v_p({g, j}) > v_p(Y_p), v_d(Y_p) > v_d(g), J' - {j} = {Y_u, z}. Y is NOT required to fail OC1.
Checks:
  RF-T: X (u {Y_x1}; x_i {Y_x(i+1)}; x_(l-1) {Y_d, z}; d {Y_p, Y_u}; p {g, j}; rest Y) is raw EFX0 iff (W-d) and (W-p);
  ORD: if Y has one receiver, u = sigma_n and d = sigma'_n; (F2) (no off-path agent other than u wants Y_d at Y) also
       when Y has two or more receivers; (W-d) iff (F1') v_d(Y_p) + v_d(Y_u) > v_d(Y_d);
  RF-T-A: where (W-p) holds and (F1') fails: u wants Y_p, u values exactly {Y_x1, Y_u, Y_d, Y_p}; (A0)-(A2); the chain
       "p takes {g, j} (+ Y_u if valued), u takes Y_p" is official at Y; X_A (p {g, j, Y_u}, u {Y_p, z}, rest Y) raw
       EFX0 whenever (A0)-(A2) hold; which hypothesis fails where X_A is not EFX0.
    run from the repository root:  python3 k4/referee/rft_ref.py P SEED [JOBS]"""
import sys, gzip, json, itertools, random
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from c13_ref import val, efx0, sd, wants, receivers, threat_J, rf_path
from cert_ref import moves
from leanrf_ref import strict_vals

def role(v, Y, i, J):
    n = len(Y)
    if not any(j != i and wants(v, j, Y[i], Y) for j in range(n)):
        return 'U'
    if not any(v[i][g] > 0 for g in J):
        return 'F'
    return 'DT' if threat_J(v, i, J, v[i][Y[i]]) else 'Dp'

def job(task):
    sets, P, seed = task
    rng = random.Random(seed); c = Counter(); n = len(sets); m = 1 + max(max(s) for s in sets)
    for t in range(P):
        v = [[0] * m for _ in range(n)]
        for i in range(n):
            for g, a in zip(sets[i], strict_vals(rng, len(sets[i]))):
                v[i][g] = a
        for sig in itertools.permutations(range(n)):
            sig = list(sig)
            Y = sd(v, sig)
            if None in Y:
                continue
            J = sorted(set(range(m)) - set(Y))
            U = receivers(v, Y)
            for u in U:
                sig2 = [u] + [a for a in sig if a != u]
                Y2 = sd(v, sig2)
                if None in Y2:
                    continue
                J2 = sorted(set(range(m)) - set(Y2))
                U2 = receivers(v, Y2)
                if len(U2) != 1:
                    continue
                if any(role(v, Y2, a, J2) == 'DT' for a in range(n)):
                    continue
                P_ = rf_path(Y, Y2, u)
                d = U2[0]
                if P_ is None or len(P_) < 3 or P_[-1] != d or Y2[d] not in J:
                    continue
                g = Y2[d]; l = len(P_) - 1
                path = set(P_)
                trades = []
                for p in range(n):
                    if p in path or role(v, Y2, p, J2) != 'Dp' or Y2[p] != Y[p]:
                        continue
                    for j in J:
                        if j == g or v[p][j] == 0:
                            continue
                        if not (v[p][g] + v[p][j] > v[p][Y[p]] and v[d][Y[p]] > v[d][g]):
                            continue
                        rest = sorted(set(J2) - {j})
                        if len(rest) != 2 or Y[u] not in rest:
                            continue
                        z = [x for x in rest if x != Y[u]][0]
                        trades.append((p, j, z))
                if not trades:
                    continue
                c['RF-T settings (Y receivers: %d)' % len(U)] += 1
                # ORD
                if len(U) == 1:
                    c['  ORD: u = sigma_n and d = sigma\'_n' if (sig[-1] == u and sig2[-1] == d) else '  ORD FAILS'] += 1
                F2 = not any(i not in path and wants(v, i, Y[d], Y) for i in range(n))
                c['  (F2) holds (Y receivers: %d)' % len(U) if F2 else '  (F2) FAILS (Y receivers: %d)' % len(U)] += 1
                ok_any = False; subcase = False
                for p, j, z in trades:
                    c['  trades'] += 1
                    X = [[y] for y in Y]
                    X[u] = [Y[P_[1]]]
                    for i in range(1, l - 1):
                        X[P_[i]] = [Y[P_[i + 1]]]
                    X[P_[l - 1]] = [Y[d], z]; X[d] = [Y[p], Y[u]]; X[p] = [g, j]
                    xv = [val(v, i, X[i]) for i in range(n)]
                    Wd = not any(i != P_[l - 1] and v[i][Y[d]] > xv[i] for i in range(n))
                    Wp = not any(i != d and v[i][Y[p]] > xv[i] for i in range(n))
                    e = efx0(v, X)
                    c['  RF-T: EFX0 == (W-d and W-p)' if e == (Wd and Wp) else '  RF-T MISMATCH'] += 1
                    F1p = v[d][Y[p]] + v[d][Y[u]] > v[d][Y[d]]
                    if F2:
                        c['  ORD: (W-d) == (F1\')' if Wd == F1p else '  (W-d) != (F1\') WITH (F2)'] += 1
                    ok_any |= e
                    if Wp and not F1p:
                        subcase = True
                        c['  [Y recv %d] RF-T-A sub-case trades' % len(U)] += 1
                        c['    [Y recv %d] u wants Y_p %s' % (len(U), wants(v, u, Y[p], Y))] += 1
                        Ru = sorted(gg for gg in range(m) if v[u][gg] > 0)
                        c['    [Y recv %d] R_u = {t, Y_u, Y_d, Y_p} %s' % (len(U), Ru == sorted({Y[P_[1]], Y[u], Y[d], Y[p]}))] += 1
                        xl1 = P_[l - 1]
                        A0 = not wants(v, xl1, Y[p], Y)
                        A1 = v[d][j] == 0 or v[d][g] + v[d][j] < v[d][Y[d]]
                        def two(i):
                            vs = sorted([v[i][g], v[i][j], v[i][Y[u]]], reverse=True)
                            return vs[0] + vs[1] > v[i][Y[i]]
                        A2 = not any(two(i) for i in range(n) if i not in (p, u, d))
                        XA = [[y] for y in Y]; XA[p] = [g, j, Y[u]]; XA[u] = [Y[p], z]
                        eA = efx0(v, XA)
                        H0 = {g, j} | ({Y[u]} if v[p][Y[u]] > 0 else set())
                        B = [{y} for y in Y]
                        st = [set(b) for b in B]; st[p] = set(H0); st[u] = {Y[p]}
                        off = any(all(set(s[i]) == st[i] for i in range(n)) for s in moves(v, B, rings=False))
                        c['    [Y recv %d] chain official %s' % (len(U), off)] += 1
                        c['    [Y recv %d] (A0) %s (A1) %s (A2) %s' % (len(U), A0, A1, A2)] += 1
                        if A0 and A1 and A2 and not eA and len(U) >= 2 and 'ex' not in c:
                            c['ex'] = 1
                            bad = [(i, jj) for i in range(n) for jj in range(n) if i != jj and len(XA[jj]) >= 2
                                   and any(val(v, i, XA[jj]) - v[i][h] > val(v, i, XA[i]) for h in XA[jj])]
                            print('  COUNTEREXAMPLE (Y has %d receivers %s): %s' % (len(U), U, json.dumps(dict(
                                sets=sets, v=v, sigma=sig, Y=Y, u=u, Y2=Y2, path=P_, d=d, p=p, g=g, j=j, z=z,
                                XA=XA, violations=bad, u_wants_Yp=wants(v, u, Y[p], Y),
                                wanters_of_Yp=[i for i in range(n) if i != p and wants(v, i, Y[p], Y)]))), flush=True)
                        if A0 and A1 and A2:
                            c['    [Y recv %d] X_A EFX0 under (A0)-(A2) %s' % (len(U), eA)] += 1
                        else:
                            c['    [Y recv %d] hypotheses fail; X_A EFX0 %s' % (len(U), eA)] += 1
                c['  [Y recv %d] X EFX0 at some trade %s' % (len(U), ok_any)] += 1
                if subcase:
                    c['  [Y recv %d] RF-T-A sub-case settings' % len(U)] += 1
    return c

def main():
    P, seed = int(sys.argv[1]), int(sys.argv[2]); jobs = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    print('$ python3 k4/referee/rft_ref.py', *sys.argv[1:], flush=True)
    d = json.load(gzip.open('results/k4_certs_5_pure.json.gz'))
    cores = [h['sets'] for h in d['cores'] if 1 + max(max(s) for s in h['sets']) == 8]
    print('pure n = 5 cores with m = 8:', len(cores), flush=True)
    tasks = [(s, P, seed * 100000 + k) for k, s in enumerate(cores)]
    C = Counter()
    with Pool(jobs) as pool:
        for c in pool.imap_unordered(job, tasks):
            C.update(c)
    C.pop('ex', None)
    for k in sorted(C):
        print('  %-60s %d' % (k, C[k]))

if __name__ == '__main__':
    main()
