"""Exact (SMT) tests of Observations S1 and S2 (k4/d1.md §7.1) at n = 4, t = 1, and of D1-H2 there.

S2 test (ROLE=S2): agents k, z, w, o.  k takes a = Y_k; z and w want a and are unfrozen; o is unfrozen and does not want
a.  o's position in the serial-dictatorship order is a parameter (before k, between k and z, between z and w, after w).
S1 test (ROLE=S1): agents k, z, w, u, all of z, w, u want a and are unfrozen.
For every structure: positive reals with these picks and wants, D = {k}, every canonical chain from k with HEAD, and no
one-absorber completion of the picks.  MODE=NONE asks only that (does such a hard all-HEAD start exist?); MODE=C2 adds
"no repair by D1-H2" (canonical chains and their extensions, minimal H0, S* owned by k, holders from the values).

    ROLE=S2|S1 MODE=NONE|C2 STRICT=0|2 MC2=0|1 SHARD=i/n python3 k4/d1/s12_smt.py [max_junk]
"""
import sys, os, itertools, collections, time, json
import z3

ROLE = os.environ.get('ROLE', 'S2'); MODE = os.environ.get('MODE', 'NONE')
MC2 = os.environ.get('MC2', '0') == '1'; STRICT = os.environ.get('STRICT', '0')
N = 4


def structures(max_junk):
    """agents 0 = k, 1 = z, 2 = w, 3 = o (S2) or u (S1); goods 0 = a = Y_k, 1, 2, 3 = picks of 1, 2, 3; junk 4.."""
    seen = set()
    picks_other = {0: [1, 2, 3], 1: [0, 2, 3], 2: [0, 1, 3], 3: [0, 1, 2]}
    for flags in itertools.product((0, 1), repeat=12):
        R = [{0}, {0, 1}, {0, 2}, ({0, 3} if ROLE == 'S1' else {3})]
        fl = iter(flags)
        for i in range(4):
            for g in picks_other[i]:
                f = next(fl)
                if f: R[i].add(g)
        if ROLE == 'S2' and 0 in R[3] and False: pass
        cap = [4 - len(r) for r in R]
        if min(cap) < 0: continue
        types = list(range(1, 16))
        def rec(i, used, counts):
            if i == len(types):
                yield list(counts); return
            t = types[i]
            for c in range(0, 4):
                nu = [used[a] + c * (t >> a & 1) for a in range(4)]
                if any(nu[a] > cap[a] for a in range(4)): break
                yield from rec(i + 1, nu, counts + [c])
        for counts in rec(0, [0] * 4, []):
            nj = sum(counts)
            if nj == 0 or nj > max_junk: continue
            RR = [set(r) for r in R]; g = 4; junk = []
            for t, c in zip(types, counts):
                for _ in range(c):
                    for a in range(4):
                        if t >> a & 1: RR[a].add(g)
                    junk.append(g); g += 1
            if not any(h in RR[0] for h in junk): continue
            # necessary for HEAD on a chain (k, u): u values a junk good; an unfrozen o that values no junk is inert
            # (Lemma CONTRACT deletes it), so S2 needs o to value junk
            need = [1, 2, 3]
            if any(not any(h in RR[i] for h in junk) for i in need): continue
            if MC2:
                if any(len(r) < 3 for r in RR): continue
                if any(sum(1 for h in RR[i] if all(h not in RR[j] for j in range(4) if j != i)) >= 2 for i in range(4)): continue
            positions = (0, 1, 2, 3) if ROLE == 'S2' else (3,)
            for pos in positions:
                key = (flags, tuple(counts), pos)
                if key in seen: continue
                seen.add(key)
                yield [sorted(r) for r in RR], junk, pos


def partial_maps(agents, pool):
    if not agents: yield {}; return
    first, rest = agents[0], agents[1:]
    for m in partial_maps(rest, pool): yield dict(m)
    for g in pool:
        for m in partial_maps(rest, [h for h in pool if h != g]):
            m = dict(m); m[first] = g; yield m


def check(R, junk, pos):
    order = [0, 1, 2]; order.insert(pos, 3)               # pos: index of agent 3 in the order (S1: last)
    x = {(i, g): z3.Real('x_%d_%d' % (i, g)) for i in range(N) for g in R[i]}
    def v(i, g): return x[(i, g)] if (i, g) in x else z3.RealVal(0)
    def V(i, S): return z3.Sum([v(i, g) for g in S]) if S else z3.RealVal(0)
    sol = z3.Solver()
    for key in x: sol.add(x[key] > 0)
    if MC2:
        for i in range(N):
            for g in R[i]: sol.add(2 * v(i, g) < V(i, R[i]))
    if STRICT == '2':
        for i in range(N):
            subs = [set(c) for r in range(1, len(R[i]) + 1) for c in itertools.combinations(R[i], r)]
            for S1, S2 in itertools.combinations(subs, 2):
                if not (S1 & S2): sol.add(V(i, sorted(S1)) != V(i, sorted(S2)))
    pick = {0: 0, 1: 1, 2: 2, 3: 3}
    taken = set()
    for i in order:
        for g in R[i]:
            if g != pick[i] and g not in taken:
                sol.add(z3.Or(v(i, pick[i]) > v(i, g), z3.And(v(i, pick[i]) == v(i, g), pick[i] < g)))
        taken.add(pick[i])
    B0 = [[i] for i in range(N)]
    p = [v(i, i) for i in range(N)]
    wanters_a = [1, 2] + ([3] if ROLE == 'S1' else [])
    for i in range(N):
        for j in range(N):
            if i == j or pick[j] not in R[i]: continue
            if j == 0 and i in wanters_a: sol.add(v(i, 0) > p[i])
            else: sol.add(v(i, pick[j]) <= p[i])          # nobody else wants anything
    J = list(junk)
    def ok(X):
        c = []
        for i in range(N):
            for j in range(N):
                if i != j:
                    for g in X[j]: c.append(V(i, X[i]) >= V(i, X[j]) - v(i, g))
        return z3.And(c)
    def frozen_at(B, i):
        if len(B[i]) != 1: return z3.BoolVal(False)
        return z3.Or([v(j, B[i][0]) > V(j, B[j]) for j in range(N) if j != i])
    def threat(i, t, S):
        return z3.Or([V(i, [g for g in S if g != h]) > t for h in S]) if len(S) >= 2 else z3.BoolVal(False)
    chains = [(0, u) for u in wanters_a]
    for path in chains:                                   # HEAD (u frozen after the chain: another wanter of a exists)
        u = path[-1]; sol.add(threat(u, v(u, 0), J + [u]))
    for o in range(N):                                    # hard
        for f in partial_maps([i for i in range(N) if i != o], J):
            X = [list(b) for b in B0]
            for i, g in f.items(): X[i].append(g)
            X[o] = X[o] + [g for g in J if g not in f.values()]
            sol.add(z3.Not(ok(X)))
    if MODE == 'C2':
        def no_sstar(B, rest):
            comps = []
            for f in partial_maps([1, 2, 3], rest):
                allowed = [z3.BoolVal(len(B[i]) <= 1) for i in f] + [z3.Not(frozen_at(B, i)) for i in f]
                X = [list(b) for b in B]
                for i, g in f.items(): X[i].append(g)
                X[0] = X[0] + [g for g in rest if g not in f.values()]
                comps.append(z3.And(allowed + [ok(X)]))
            return z3.Not(z3.Or(comps))
        def minimal(H0):
            return z3.And([V(0, list(H0)) > p[0]] + [z3.Not(V(0, [h for h in H0 if h != e]) > p[0]) for e in H0])
        for path in chains:
            u = path[-1]
            for ext in [None] + [(u2, S) for u2 in wanters_a if u2 != u for sz in (0, 1, 2) for S in itertools.combinations(J, sz)]:
                if ext is None:
                    Pi = J + [u]; cond = z3.BoolVal(True)
                else:
                    u2, S = ext; Pi = [h for h in J if h not in S] + [u2]; cond = V(u2, [u] + list(S)) > p[u2]
                kp = [h for h in Pi if h in R[0]]
                for r in range(1, len(kp) + 1):
                    for H0 in itertools.combinations(kp, r):
                        B = [list(b) for b in B0]; B[u] = [0]; B[0] = list(H0)
                        if ext is not None: B[ext[0]] = [u] + list(ext[1])
                        sol.add(z3.Implies(z3.And(minimal(H0), cond), no_sstar(B, [h for h in Pi if h not in H0])))
    return sol


if __name__ == '__main__':
    maxj = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    print('$ ROLE=%s MODE=%s MC2=%d STRICT=%s SHARD=%s python3 k4/d1/s12_smt.py' % (ROLE, MODE, MC2, STRICT, os.environ.get('SHARD')), *sys.argv[1:], flush=True)
    C = collections.Counter(); t0 = time.time(); shard = os.environ.get('SHARD')
    for idx, (R, junk, pos) in enumerate(structures(maxj)):
        if shard:
            si, sn = map(int, shard.split('/'))
            if idx % sn != si: continue
        sol = check(R, junk, pos); r = sol.check(); C['structures'] += 1; C[str(r)] += 1
        if r == z3.sat:
            m = sol.model()
            vals = [[str(m.eval(z3.Real('x_%d_%d' % (i, g)), model_completion=True)) for g in R[i]] for i in range(N)]
            print('SAT', json.dumps(R), json.dumps(vals), 'pos', pos, flush=True)
        if C['structures'] % 500 == 0: print(C['structures'], dict(C), '%.0f s' % (time.time() - t0), flush=True)
    for kk in sorted(C): print(kk, C[kk])
    print('time %.0f s' % (time.time() - t0))
