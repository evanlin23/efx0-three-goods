"""Second, independently written SMT encoding (E2) of the three-agent core check of k4/d1.md §6.

Written from the definitions without reusing core3_smt.py (E1):
  - EFX0 is written as v_i(X_i) >= v_i(X_j) - v_i(g) for every g in X_j (E1 uses the "threat" form with a minimum);
  - holders and frozen agents at every state are computed symbolically from the values (E1 hard-codes them);
  - structures are enumerated agent by agent and deduplicated by a canonical form (E1 enumerates junk-type multisets);
  - the one-absorber completions are generated as injective partial maps (E1 uses combinations x permutations).
Same question: positive reals such that the order (k, z, w) = (0, 1, 2) gives picks (a, y_z, y_w) = (0, 1, 2), z and
w want a and are unfrozen, both chains (0, 1), (0, 2) have HEAD, the picks have no one-absorber completion, and the
repair family (MODE=CANON: canonical chains; MODE=HJ: also the head taking one junk good) never gives an S* completion
owned by k with a minimal improving H0.

    MODE=CANON|HJ|NONE MC2=0|1 STRICT=0|1|2 python3 k4/d1/core3_smt2.py [max_junk]
"""
import sys, os, itertools, collections, time, json
import z3

MODE = os.environ.get('MODE', 'HJ'); MC2 = os.environ.get('MC2', '0') == '1'; STRICT = os.environ.get('STRICT', '0')


def all_structures(max_junk):
    seen = set()
    for nj in range(1, max_junk + 1):
        junk = list(range(3, 3 + nj))
        for owners in itertools.product(range(1, 8), repeat=nj):          # bitmask over {k, z, w} per junk good
            if owners != tuple(sorted(owners)): continue                     # canonical: sorted masks
            for extra in itertools.product((0, 1), repeat=4):              # k~y_z, k~y_w, z~y_w, w~y_z
                R = [{0}, {0, 1}, {0, 2}]
                if extra[0]: R[0].add(1)
                if extra[1]: R[0].add(2)
                if extra[2]: R[1].add(2)
                if extra[3]: R[2].add(1)
                for g, mask in zip(junk, owners):
                    for i in range(3):
                        if mask >> i & 1: R[i].add(g)
                if any(len(r) > 4 for r in R): continue
                if not any(owners[t] & 1 for t in range(nj)): continue       # k values some junk
                if MC2:
                    if any(len(r) < 3 for r in R): continue
                    if any(sum(1 for g in R[i] if not any(g in R[j] for j in range(3) if j != i)) >= 2 for i in range(3)): continue
                key = (tuple(sorted(owners)), extra)
                if key in seen: continue
                seen.add(key)
                yield [sorted(r) for r in R], junk


def check(R, junk):
    n = 3; goods = [0, 1, 2] + junk
    x = {(i, g): z3.Real('x_%d_%d' % (i, g)) for i in range(n) for g in R[i]}
    def v(i, g): return x[(i, g)] if (i, g) in x else z3.RealVal(0)
    def V(i, S): return z3.Sum([v(i, g) for g in S]) if S else z3.RealVal(0)
    sol = z3.Solver()
    for key in x: sol.add(x[key] > 0)
    if MC2:
        for i in range(n):
            for g in R[i]: sol.add(2 * v(i, g) < V(i, R[i]))
    if STRICT == '1':
        for i in range(n):
            for g, h in itertools.combinations(R[i], 2): sol.add(v(i, g) != v(i, h))
    if STRICT == '2':
        for i in range(n):
            subs = [set(c) for r in range(1, len(R[i]) + 1) for c in itertools.combinations(R[i], r)]
            for S1, S2 in itertools.combinations(subs, 2):
                if not (S1 & S2): sol.add(V(i, sorted(S1)) != V(i, sorted(S2)))
    def ranks_above(i, g, h): return z3.Or(v(i, g) > v(i, h), z3.And(v(i, g) == v(i, h), g < h))
    # serial dictatorship (0, 1, 2) picks (0, 1, 2)
    taken = set()
    for i, pick in ((0, 0), (1, 1), (2, 2)):
        for g in R[i]:
            if g != pick and g not in taken: sol.add(ranks_above(i, pick, g))
        taken.add(pick)
    picks = {0: 0, 1: 1, 2: 2}
    def ok(X):
        """raw EFX0 in the form v_i(X_i) >= v_i(X_j) - v_i(g)"""
        conds = []
        for i in range(n):
            for j in range(n):
                if i == j: continue
                for g in X[j]:
                    conds.append(V(i, X[i]) >= V(i, X[j]) - v(i, g))
        return z3.And(conds)
    def frozen_at(B, i):
        if len(B[i]) != 1: return z3.BoolVal(False)
        return z3.Or([v(j, B[i][0]) > V(j, B[j]) for j in range(n) if j != i])
    B0 = [[0], [1], [2]]
    # z, w want a; z, w unfrozen; k frozen (implied)
    sol.add(v(1, 0) > v(1, 1), v(2, 0) > v(2, 2))
    sol.add(z3.Not(frozen_at(B0, 1)), z3.Not(frozen_at(B0, 2)))
    J = list(junk)
    # HEAD on both chains (k, u): u frozen after the chain (implied: the other wanter still wants a) and threatened
    for u in (1, 2):
        Pi = J + [picks[u]]
        sol.add(z3.Or([V(u, [g for g in Pi if g != h]) > v(u, 0) for h in Pi]))
    # hard: every one-absorber completion fails
    def partial_maps(agents, pool):
        if not agents: yield {}; return
        first, rest = agents[0], agents[1:]
        for m in partial_maps(rest, pool): yield dict(m)
        for g in pool:
            for m in partial_maps(rest, [h for h in pool if h != g]):
                m = dict(m); m[first] = g; yield m
    for o in range(n):
        for f in partial_maps([i for i in range(n) if i != o], J):
            X = [list(b) for b in B0]
            for i, g in f.items(): X[i].append(g)
            X[o] = X[o] + [g for g in J if g not in f.values()]
            sol.add(z3.Not(ok(X)))
    # repairs
    if MODE != 'NONE':
        for u in (1, 2):
            other = 3 - u
            Pi = J + [picks[u]]
            for g in [None] + (J if MODE in ('HJ', 'H2') else []):
                pool = [h for h in Pi if h != g]
                kpool = [h for h in pool if h in R[0]]
                for r in range(1, len(kpool) + 1):
                    for H0 in itertools.combinations(kpool, r):
                        imp = V(0, list(H0)) > v(0, 0)
                        minimal = z3.And([imp] + [z3.Not(V(0, [h for h in H0 if h != e]) > v(0, 0)) for e in H0])
                        B = [sorted(H0), [0] + ([g] if g is not None else []), None]
                        B = [list(H0), None, None]
                        B[u] = [0] + ([g] if g is not None else [])
                        B[other] = [picks[other]]
                        rest = [h for h in pool if h not in H0]
                        comps = []
                        for f in partial_maps([i for i in range(n) if i != 0], rest):
                            # S*: only unfrozen agents holding at most one good may take a good
                            allowed = [z3.And(len(B[i]) <= 1, z3.Not(frozen_at(B, i))) if True else None for i in f]
                            allowed = [z3.BoolVal(len(B[i]) <= 1) for i in f] + [z3.Not(frozen_at(B, i)) for i in f]
                            X = [list(b) for b in B]
                            for i, h in f.items(): X[i].append(h)
                            X[0] = X[0] + [h for h in rest if h not in f.values()]
                            comps.append(z3.And(allowed + [ok(X)]))
                        sol.add(z3.Implies(minimal, z3.Not(z3.Or(comps))))
    if MODE in ('C2', 'H2'):
        # the double chain (k, u, u2): u takes a; u2 takes u's pick plus junk S (improving for u2); k takes H0
        for u in (1, 2):
            u2 = 3 - u
            for size in (0, 1, 2):
                for S in itertools.combinations(J, size):
                    better_u2 = V(u2, [picks[u]] + list(S)) > v(u2, picks[u2])
                    pool = [h for h in J + [picks[u2]] if h not in S]
                    kpool = [h for h in pool if h in R[0]]
                    for r in range(1, len(kpool) + 1):
                        for H0 in itertools.combinations(kpool, r):
                            imp = V(0, list(H0)) > v(0, 0)
                            minimal = z3.And([imp] + [z3.Not(V(0, [h for h in H0 if h != e]) > v(0, 0)) for e in H0])
                            B = [list(H0), None, None]
                            B[u] = [0]; B[u2] = [picks[u]] + list(S)
                            rest = [h for h in pool if h not in H0]
                            comps = []
                            for f in partial_maps([1, 2], rest):
                                allowed = [z3.BoolVal(len(B[i]) <= 1) for i in f] + [z3.Not(frozen_at(B, i)) for i in f]
                                X = [list(b) for b in B]
                                for i, h in f.items(): X[i].append(h)
                                X[0] = X[0] + [h for h in rest if h not in f.values()]
                                comps.append(z3.And(allowed + [ok(X)]))
                            sol.add(z3.Implies(z3.And(minimal, better_u2), z3.Not(z3.Or(comps))))
    return sol.check()


if __name__ == '__main__':
    maxj = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    print('$ MODE=%s MC2=%d STRICT=%s python3 k4/d1/core3_smt2.py' % (MODE, MC2, STRICT), *sys.argv[1:], flush=True)
    C = collections.Counter(); t0 = time.time()
    for R, junk in all_structures(maxj):
        r = check(R, junk); C['structures'] += 1; C[str(r)] += 1
        if r == z3.sat: print('SAT', json.dumps(R), flush=True)
    for kk in sorted(C): print(kk, C[kk])
    print('time %.0f s' % (time.time() - t0))
