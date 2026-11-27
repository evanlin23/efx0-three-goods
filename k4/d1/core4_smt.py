"""Exact (SMT) check of Conjecture D1-H2 on the four-agent core with t = 2 (k4/d1.md §7.3).

Agents k = 0, x = 1, z = 2, w = 3, serial-dictatorship order (0, 1, 2, 3), picks Y_i = i; junk goods 4, 5, ....
x wants Y_k = 0; z and w want a = Y_x = 1 and are unfrozen; x values no junk (it is frozen and not dangerous); k values
junk.  z and w may also value Y_k = 0, and then either want it or not (part of the structure).  For every structure the
solver looks for positive reals with: the picks, the want relation of the structure, every canonical chain from k
having HEAD, no one-absorber completion of the picks, and no repair by D1-H2 (each canonical chain, and its extension
by another unfrozen wanter of the head's new good taking the head's pick plus junk, with every minimal improving H0;
S* completion owned by k, holders computed from the values).

    MODE=NONE|CANON|C2 MC2=0|1 STRICT=0|2 python3 k4/d1/core4_smt.py [max_junk]
"""
import sys, os, itertools, collections, time, json
import z3

MODE = os.environ.get('MODE', 'C2'); MC2 = os.environ.get('MC2', '0') == '1'; STRICT = os.environ.get('STRICT', '0')
N = 4; KK, XX, ZZ, WW = 0, 1, 2, 3


def structures(max_junk):
    seen = set()
    # flags: k values 1, 2, 3; x values 2, 3; z values 0, 3; w values 0, 2; z wants 0; w wants 0
    for kf in itertools.product((0, 1), repeat=3):
        for xf in itertools.product((0, 1), repeat=2):
            for zf in itertools.product((0, 1), repeat=2):
                for wf in itertools.product((0, 1), repeat=2):
                    for zw0 in ((0, 1) if zf[0] else (0,)):
                        for ww0 in ((0, 1) if wf[0] else (0,)):
                            base = [{0} | {g for g, f in zip((1, 2, 3), kf) if f},
                                    {0, 1} | {g for g, f in zip((2, 3), xf) if f},
                                    {1, 2} | {g for g, f in zip((0, 3), zf) if f},
                                    {1, 3} | {g for g, f in zip((0, 2), wf) if f}]
                            cap = [4 - len(r) for r in base]
                            if min(cap) < 0: continue
                            # junk types: nonempty subsets of {k, z, w} as bitmasks over agents 0, 2, 3
                            types = [m for m in range(1, 16) if not (m >> 1 & 1)]
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
                                R = [set(r) for r in base]; g = 4; junk = []
                                for t, c in zip(types, counts):
                                    for _ in range(c):
                                        for a in range(4):
                                            if t >> a & 1: R[a].add(g)
                                        junk.append(g); g += 1
                                if not any(h in R[0] for h in junk): continue
                                if MC2:
                                    if any(len(r) < 3 for r in R): continue
                                    if any(sum(1 for h in R[i] if all(h not in R[j] for j in range(4) if j != i)) >= 2 for i in range(4)): continue
                                key = (kf, xf, zf, wf, zw0, ww0, tuple(counts))
                                if key in seen: continue
                                seen.add(key)
                                yield [sorted(r) for r in R], junk, (zw0, ww0)


def partial_maps(agents, pool):
    if not agents: yield {}; return
    first, rest = agents[0], agents[1:]
    for m in partial_maps(rest, pool): yield dict(m)
    for g in pool:
        for m in partial_maps(rest, [h for h in pool if h != g]):
            m = dict(m); m[first] = g; yield m


def check(R, junk, wants0):
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
    def above(i, g, h): return z3.Or(v(i, g) > v(i, h), z3.And(v(i, g) == v(i, h), g < h))
    for i in range(N):                          # SD with order (0, 1, 2, 3): agent i picks good i
        for g in R[i]:
            if g >= i and g != i: sol.add(above(i, i, g))
    B0 = [[i] for i in range(N)]
    p = [v(i, i) for i in range(N)]
    def wants(i, g, B): return v(i, g) > V(i, B[i])
    # the want relation at the picks
    sol.add(wants(XX, 0, B0), wants(ZZ, 1, B0), wants(WW, 1, B0))
    sol.add(z3.Not(wants(ZZ, 3, B0)) if 3 in R[ZZ] else z3.BoolVal(True), z3.Not(wants(WW, 2, B0)) if 2 in R[WW] else z3.BoolVal(True))
    if 0 in R[ZZ]: sol.add(wants(ZZ, 0, B0) if wants0[0] else z3.Not(wants(ZZ, 0, B0)))
    if 0 in R[WW]: sol.add(wants(WW, 0, B0) if wants0[1] else z3.Not(wants(WW, 0, B0)))
    # (k wants nothing and x wants nothing but 0: forced by SD; nobody wants 2 or 3 except as excluded above)
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
    # canonical chains from k (heads unfrozen): (0,1,2), (0,1,3), and (0,2)/(0,3) when z/w want 0
    chains = [(0, 1, 2), (0, 1, 3)] + [(0, u) for u, f in ((2, wants0[0]), (3, wants0[1])) if f]
    wanters = {0: [1] + [u for u, f in ((2, wants0[0]), (3, wants0[1])) if f], 1: [2, 3]}
    def state(path, H0, ext=None):
        B = [list(b) for b in B0]
        for i in range(1, len(path)): B[path[i]] = [path[i - 1]]
        B[0] = list(H0)
        if ext is not None:
            u2, S = ext; B[u2] = [path[-1]] + list(S)
        return B
    for path in chains:
        u = path[-1]; b = path[-2]
        Pi = J + [u]
        # HEAD: u frozen after the chain and threatened by Pi at v_u(b); frozen-ness at a state with any H0 is the same
        # (k's value only rises), so test it with k holding the whole pool
        Bt = state(path, [h for h in Pi if h in R[0]])
        sol.add(z3.And(frozen_at(Bt, u), threat(u, v(u, b), Pi)))
    # hard
    for o in range(N):
        for f in partial_maps([i for i in range(N) if i != o], J):
            X = [list(bb) for bb in B0]
            for i, g in f.items(): X[i].append(g)
            X[o] = X[o] + [g for g in J if g not in f.values()]
            sol.add(z3.Not(ok(X)))
    def no_sstar(B, pool_rest):
        comps = []
        for f in partial_maps([i for i in range(1, N)], pool_rest):
            allowed = [z3.BoolVal(len(B[i]) <= 1) for i in f] + [z3.Not(frozen_at(B, i)) for i in f]
            X = [list(bb) for bb in B]
            for i, g in f.items(): X[i].append(g)
            X[0] = X[0] + [g for g in pool_rest if g not in f.values()]
            comps.append(z3.And(allowed + [ok(X)]))
        return z3.Not(z3.Or(comps))
    def minimal(H0):
        return z3.And([V(0, list(H0)) > p[0]] + [z3.Not(V(0, [h for h in H0 if h != e]) > p[0]) for e in H0])
    if MODE in ('CANON', 'C2'):
        for path in chains:
            u = path[-1]; b = path[-2]
            Pi = J + [u]
            kp = [h for h in Pi if h in R[0]]
            for r in range(1, len(kp) + 1):
                for H0 in itertools.combinations(kp, r):
                    B = state(path, H0)
                    sol.add(z3.Implies(minimal(H0), no_sstar(B, [h for h in Pi if h not in H0])))
            if MODE == 'C2':
                for u2 in wanters[b]:
                    if u2 in path or u2 == 1: continue            # u2 must be an unfrozen wanter off the chain
                    for sz in (0, 1, 2):
                        for S in itertools.combinations(J, sz):
                            better = V(u2, [u] + list(S)) > p[u2]
                            Pi2 = [h for h in J if h not in S] + [u2]
                            kp = [h for h in Pi2 if h in R[0]]
                            for r in range(1, len(kp) + 1):
                                for H0 in itertools.combinations(kp, r):
                                    B = state(path, H0, (u2, S))
                                    sol.add(z3.Implies(z3.And(minimal(H0), better), no_sstar(B, [h for h in Pi2 if h not in H0])))
    return sol


if __name__ == '__main__':
    maxj = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    print('$ MODE=%s MC2=%d STRICT=%s python3 k4/d1/core4_smt.py' % (MODE, MC2, STRICT), *sys.argv[1:], flush=True)
    C = collections.Counter(); t0 = time.time()
    shard = os.environ.get('SHARD')            # 'i/n': only structures with index = i mod n
    only = None
    if os.environ.get('ONLY'):                 # a log of a MODE=NONE run: only its SAT structures
        only = set()
        for line in open(os.environ['ONLY']):
            if line.startswith('SAT'):
                only.add(line.split(' wants0 ')[0].split(' ', 2)[1] + ' ' + line.split(' wants0 ')[1].strip())
    for idx, (R, junk, w0) in enumerate(structures(maxj)):
        if shard:
            si, sn = map(int, shard.split('/'))
            if idx % sn != si: continue
        if only is not None and (json.dumps(R) + ' ' + str(w0)) not in only: continue
        sol = check(R, junk, w0); r = sol.check(); C['structures'] += 1; C[str(r)] += 1
        if r == z3.sat:
            m = sol.model()
            vals = [[str(m.eval(z3.Real('x_%d_%d' % (i, g)), model_completion=True)) for g in R[i]] for i in range(N)]
            print('SAT', json.dumps(R), json.dumps(vals), 'wants0', w0, flush=True)
        if C['structures'] % 200 == 0: print(C['structures'], dict(C), '%.0f s' % (time.time() - t0), flush=True)
    for kk in sorted(C): print(kk, C[kk])
    print('time %.0f s' % (time.time() - t0))
