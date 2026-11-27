#!/usr/bin/env python3
"""Referee probe of Lemma UNTANGLE (kgen/rounds.md §4.13 on proof/kgen-rounds at 50c1fc44). Own code.

Instances: random connected cores with distinct subset sums (<= 4 relevant goods per agent), every perfect SD start Y,
every MD raw-EFX0 allocation X (brute force), every needy keep-and-add pair (q pickless; Y_q ∈ X_v; Y_v ∈ X_v;
v_v(X_v - Y_v) <= p_v). Moves: U0 (Y_q to q), U1(h) (Y_q to q, h ∈ X_q to v), U1'(h, w) (h to w ∉ {q, v}).
Checked: the PROVED parts (Φ's first coordinate +2; MD; q's strict gain; q's EFX0 conditions; pairs between unchanged
bundles; under U0 the conditions toward v's shrunken bundle) must never fail. Classified: every failing EFX0 pair of
U0 / U1(h) as (O1) toward q's new bundle, (O2) v toward another bundle, (O3) a third agent toward v's new bundle
(U1), or OTHER (must be 0). Rules for h tested when U0 fails: 'O1max' (the good of X_q that the U0 (O1)-violators
value most, by their maximum), 'vmax' (v's most valued good of X_q), 'qmin' (q's least valued), 'sum' (largest total
value to the other agents); 'exists' = some h. Smallest pair where U0 and every U1(h) fail is printed."""
import itertools, json, sys, random
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, efx0, sd
from oc1hall_ref import threatened
from roundsimple_ref import strict_dss

def failing_pairs(v, X):
    n = len(X); out = []
    for i in range(n):
        t = val(v, i, X[i])
        for j in range(n):
            if i != j and len(X[j]) >= 2 and threatened(v, i, X[j], t):
                out.append((i, j))
    return out

def picks_held(Y, X):
    return [sum(1 for y in Y if y in X[b]) for b in range(len(X))]

def phi1(Y, X):
    return sum(1 for c in picks_held(Y, X) if c == 1)

def classify(fails, q, v, U1):
    kinds = set()
    for i, j in fails:
        if j == q and i != q:
            kinds.add("O1")
        elif i == v and j != q:
            kinds.add("O2")
        elif U1 and j == v and i not in (q, v):
            kinds.add("O3")
        else:
            kinds.add("OTHER")
    return kinds

def job(args):
    v, Ys = args
    n = len(v); m = len(v[0]); c = Counter(); ex = {}
    for Y in Ys:
        p = [v[i][Y[i]] for i in range(n)]; picks = set(Y)
        for f in itertools.product(range(n), repeat=m):
            X = [set() for _ in range(n)]
            for g, a in enumerate(f):
                X[a].add(g)
            if any(val(v, i, X[i]) < p[i] for i in range(n)) or not efx0(v, X):
                continue
            for q in range(n):
                if X[q] & picks:
                    continue
                vv = next(b for b in range(n) if Y[q] in X[b])
                if Y[vv] not in X[vv] or val(v, vv, X[vv] - {Y[vv]}) > p[vv]:
                    continue
                c["needy_pairs"] += 1
                base_phi = phi1(Y, X)
                def mk(h=None, w=None):
                    Z = [set(b) for b in X]; Z[vv].discard(Y[q]); Z[q].add(Y[q])
                    if h is not None:
                        Z[q].discard(h); Z[w].add(h)
                    return Z
                def proved(Z, U1):
                    bad = []
                    if phi1(Y, Z) != base_phi + 2: bad.append("phi")
                    if any(val(v, i, Z[i]) < p[i] for i in range(n)): bad.append("MD")
                    if not val(v, q, Z[q]) > val(v, q, X[q]): bad.append("q_gain")
                    fl = failing_pairs(v, Z)
                    if any(i == q for i, j in fl): bad.append("q_conditions")
                    ch = {q, vv}
                    if any(i not in ch and j not in ch for i, j in fl): bad.append("unchanged")
                    if not U1 and any(j == vv and i != vv for i, j in fl): bad.append("toward_shrunken_v")
                    return bad, fl
                Z0 = mk(); bad, fl0 = proved(Z0, False)
                for b in bad:
                    c["PROVED_PART_FAIL_U0_" + b] += 1
                k0 = classify(fl0, q, vv, False)
                c["U0_ok"] += not fl0
                c["U0_OTHER_FAIL"] += "OTHER" in k0
                if fl0:
                    c["U0_fails_" + "+".join(sorted(k0))] += 1
                if not fl0:
                    continue
                res = {}
                for h in sorted(X[q]):
                    Z = mk(h, vv); bad, fl = proved(Z, True)
                    for b in bad:
                        c["PROVED_PART_FAIL_U1_" + b] += 1
                    k = classify(fl, q, vv, True); c["U1_OTHER_FAIL"] += "OTHER" in k
                    res[h] = (not fl, k)
                ok_h = [h for h in res if res[h][0]]
                viol = [i for i, j in fl0 if j == q]
                rules = dict(
                    O1max=max(sorted(X[q]), key=lambda g: max([v[i][g] for i in viol] or [0])) if X[q] else None,
                    vmax=max(sorted(X[q]), key=lambda g: v[vv][g]) if X[q] else None,
                    qmin=min(sorted(X[q]), key=lambda g: v[q][g]) if X[q] else None,
                    sum=max(sorted(X[q]), key=lambda g: sum(v[i][g] for i in range(n) if i != q)) if X[q] else None)
                c["U0_fail_cases"] += 1; c["rule_exists"] += bool(ok_h)
                for r, h in rules.items():
                    c["rule_" + r] += h in ok_h
                tag = None
                if not ok_h:
                    allk = set().union(*(res[h][1] for h in res)) if res else set()
                    c["no_U1_blocks_" + "+".join(sorted(allk))] += 1
                    w_ok = any(not failing_pairs(v, mk(h, w)) for h in sorted(X[q]) for w in range(n) if w not in (q, vv))
                    c["no_U1_but_U1prime"] += w_ok
                    tag = "blocks_" + "+".join(sorted(allk)) + ("_U1prime_works" if w_ok else "_nothing_works")
                elif rules["O1max"] not in ok_h:
                    tag = "O1max_rule_fails_but_some_h_works"
                if tag is not None and (tag not in ex or m < ex[tag]["m"]):
                    ex[tag] = dict(n=n, m=m, v=v, picks=Y, X=[sorted(b) for b in X], q=q, v_agent=vv,
                                   U0_fails=sorted(map(list, fl0)), U1=[(h, sorted(res[h][1])) for h in res], ok_h=ok_h)
    return c, ex

def jobs(N, seed, n, m):
    rng = random.Random(seed)
    for _ in range(N):
        v = strict_dss(rng, n, m)
        Ys = {tuple(sd(v, list(o))) for o in itertools.permutations(range(n))}
        Ys = [list(Y) for Y in Ys if None not in Y]
        if Ys:
            yield v, Ys

def main(N, seed, n, m, procs):
    c = Counter(); ex = {}
    with Pool(procs) as pool:
        for cc, e in pool.imap_unordered(job, jobs(N, seed, n, m), chunksize=2):
            c.update(cc)
            for t, d in e.items():
                ex.setdefault(t, d)
    print(json.dumps(dict(source=f"Lemma UNTANGLE probe N={N} seed={seed} n={n} m={m}", **dict(sorted(c.items())))))
    for t in sorted(ex):
        print("EXAMPLE", t, json.dumps(ex[t]))

if __name__ == "__main__":
    main(*map(int, sys.argv[1:6]))
