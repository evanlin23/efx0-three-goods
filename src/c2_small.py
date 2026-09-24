"""Bundles of at most two goods in cores with n <= 4, and conjecture D for disconnected cores with n <= 6
(proof/step0-lemmas).
1. Model C2 (every bundle has at most two goods) on every connected core with 2 <= n <= 4 and 3 <= m <= 2n, under
   every ranking profile, two independent ways: the CEGAR search of frontier.py (SAT, L5 model), and a SAT-free brute
   force written here that enumerates every allocation with bundles <= 2 and decides each agent's safety for each of
   its 6 rankings from the raw EFX0 definition under three balanced realizations (they must agree). Both must report
   the same hypergraphs as failing; the brute force lists every failing profile. Certificates for the passing cores
   (C2 allocations covering all profiles) go to certs_c2_2_3_4.json.gz for tools/check_certs.py.
2. Conjecture D for disconnected cores. L6 composes EFX0 allocations of the components, but a union of allocations
   with one large bundle each can have several, so D for disconnected cores does not follow from D for connected
   ones. With n <= 6 every component has >= 2 agents, so at most two components have >= 3 agents, and that happens
   only for two components of 3 agents. All 2-agent cores pass C2 (part 1), so D can only fail for a disjoint union
   of two 3-agent cores that both fail C2; part 1 finds one such core, H3 = {0,1,2}, {0,1,3}, {0,1,4}. Its disjoint
   union with itself (n = 6, m = 10) is searched over all 6^6 profiles in model C3 (at most one bundle of more than
   two goods) and the coverage is re-checked with tools/check_certs.py's raw-definition masks.
3. The same C3 test for one profile of two disjoint copies of the X2 core (n = 12), where each copy needs a large
   bundle.
Usage: python c2_small.py   (about a minute; writes certs_c2_2_3_4.json.gz and certs_d_disconnected.json.gz)"""
import sys, os, gzip, json, itertools, collections
import numpy as np
from frontier import solve_core, cegar, certify, build, PERMS
from cores_nauty import gen_cores_nauty
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'tools'))
from check_certs import uncovered

REAL = [(4, 3, 2), (10, 9, 2), (6, 5, 4)]                       # balanced realizations of a > b > c (exact integers)

def raw_safe(val, bundles, i):
    own = sum(val.get(g, 0) for g in bundles[i])
    return all(sum(val.get(h, 0) for h in B) - val.get(g, 0) <= own
               for j, B in enumerate(bundles) if j != i for g in B)

def pair_partitions(goods):
    if not goods: yield []; return
    g, rest = goods[0], goods[1:]
    for p in pair_partitions(rest): yield [[g]] + p
    for k, h in enumerate(rest):
        for p in pair_partitions(rest[:k] + rest[k + 1:]): yield [[g, h]] + p

def brute_c2(n, m, sets):
    """Boolean array over the 6^n ranking profiles (axis i = agent i's ranking, as PERMS): covered by some EFX0
    allocation with all bundles <= 2. Every such allocation is enumerated (partition into blocks of <= 2 goods,
    padded with empty bundles, every assignment of the n slots to the agents)."""
    cov = np.zeros((6,) * n, dtype=bool)
    for p in pair_partitions(list(range(m))):
        if len(p) > n: continue
        slots = p + [[] for _ in range(n - len(p))]
        ok = np.zeros((n, n, 6), dtype=bool)                      # ok[i, s, k]: agent i holding slot s, ranking k
        for i, S in enumerate(sets):
            for s in range(n):
                bundles = [slots[s]] + slots[:s] + slots[s + 1:]
                for k, q in enumerate(PERMS):
                    res = {raw_safe(dict(zip((S[q[0]], S[q[1]], S[q[2]]), r)), bundles, 0) for r in REAL}
                    if len(res) != 1: raise SystemExit("realizations disagree")
                    ok[i, s, k] = res.pop()
        for sigma in set(itertools.permutations(range(n))):
            idx = [np.flatnonzero(ok[i, sigma[i]]) for i in range(n)]
            if all(len(x) for x in idx): cov[np.ix_(*idx)] = True
    return cov

if __name__ == '__main__':
    certs, fail_sat, fail_brute, bad = [], [], [], 0
    for n in (2, 3, 4):
        for m in range(3, 2 * n + 1):
            tally = collections.Counter()
            for pi, sets in gen_cores_nauty(n, m):
                rec, cert = solve_core((n, m, pi, sets, ['C2']))
                cov = brute_c2(n, m, sets); nbad = int((~cov).sum())
                sat_fails = rec['modes']['C2']['status'] == 'FAIL'
                if cert: certs.append(cert)
                if sat_fails: fail_sat.append((n, m, sets))
                if nbad:
                    fail_brute.append((n, m, sets))
                    first = [int(k) for k in np.argwhere(~cov)[0]]
                    trip = [tuple(S[q] for q in PERMS[k]) for S, k in zip(sets, first)]
                    print(f"  n={n} m={m} {sets}: {nbad} of {6 ** n} profiles have no size-<=2 EFX0 allocation "
                          f"(brute force); e.g. (agent: a > b > c) {trip}; SAT search: {rec['modes']['C2']['status']}"
                          f" at {[tuple(S[q] for q in PERMS[k]) for S, k in zip(sets, rec['modes']['C2']['bad'])] if sat_fails else '-'}")
                    if sat_fails and cov[tuple(rec['modes']['C2']['bad'])]: bad += 1     # SAT says fail, brute says ok
                tally['C2 ok' if not nbad else 'C2 fails'] += 1
            print(f"n={n} m={m}: {dict(tally)}", flush=True)
    agree = fail_sat == fail_brute and bad == 0
    print(f"connected cores with 2 <= n <= 4: {len(certs)} pass C2 under every profile, {len(fail_brute)} do not; "
          f"SAT search and brute force agree on which: {'YES' if agree else 'NO'}")
    with gzip.open('certs_c2_2_3_4.json.gz', 'wt') as f: json.dump(certs, f)

    # part 2: two disjoint copies of H3, all 6^6 profiles, model C3
    H3 = [(0, 1, 2), (0, 1, 3), (0, 1, 4)]
    two = H3 + [tuple(g + 5 for g in S) for S in H3]
    st, _, masks, allocs = cegar(6, 10, two, 'C3')
    rec = {'n': 6, 'm': 10, 'sets': two, 'mode': 'C3', 'allocations': allocs}
    unc_sat, unc_raw = certify(6, masks) if st == 'OK' else -1, uncovered(rec)
    large = max(sum(c > 2 for c in collections.Counter(X).values()) for X in allocs)
    ok2 = st == 'OK' and unc_sat == 0 and unc_raw == 0 and large <= 1
    print(f"H3 + H3 (disconnected, n = 6, m = 10), model C3 over all 46656 profiles: {st}, {len(allocs)} allocations, "
          f"uncovered profiles {unc_sat} (masks from the search) / {unc_raw} (tools/check_certs.py raw masks), "
          f"max number of bundles with > 2 goods: {large}")
    with gzip.open('certs_d_disconnected.json.gz', 'wt') as f: json.dump([rec], f)

    # part 3: two disjoint copies of X2, the profile of the X2 example
    X2 = [(1, 0, 6), (1, 0, 7), (2, 0, 8), (3, 0, 9), (2, 4, 5), (3, 4, 5)]
    tw = X2 + [tuple(g + 10 for g in t) for t in X2]
    sets = [tuple(sorted(t)) for t in tw]
    prof = [PERMS.index(tuple(S.index(g) for g in t)) for S, t in zip(sets, tw)]
    S, sel, x = build(12, 20, sets, 'C3')
    ok3 = S.solve(assumptions=[sel[(i, prof[i])] for i in range(12)])
    mdl = set(l for l in S.get_model() if l > 0)
    X = [next(j for j in range(12) if x(g, j) in mdl) for g in range(20)]
    B = [[g for g in range(20) if X[g] == j] for j in range(12)]
    vs = [[dict(zip(t, r)) for t in tw] for r in REAL]
    ok3 = ok3 and all(raw_safe(v[i], B, i) for v in vs for i in range(12)) and sum(len(b) > 2 for b in B) <= 1
    print(f"X2 + X2 (n = 12, m = 20), X2's profile on both copies: EFX0 allocation with at most one bundle of > 2 "
          f"goods (raw definition re-checked): {B}" if ok3 else "X2 + X2: NOT FOUND")
    sys.exit(0 if agree and ok2 and ok3 else 1)
