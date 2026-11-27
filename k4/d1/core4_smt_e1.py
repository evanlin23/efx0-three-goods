"""Second, independently written encoding (E1 style) of the four-agent t = 2 core check of k4/d1.md §7.3; compare
k4/d1/core4_smt.py (E2 style).  Differences: EFX0 in the threat form (sum minus the cheapest good), structures
enumerated good by good with a sorted canonical form, the one-absorber placements as combinations x permutations, and
unfrozen-ness written as a conjunction over the other agents.

Agents k = 0, x = 1, z = 2, w = 3, order (0, 1, 2, 3), picks Y_i = i, junk 4.. .  x wants 0; z and w want 1 and are
unfrozen; x values no junk; z, w may value 0 and then want it or not (flags).  MODE=NONE: hard + every canonical chain
with HEAD; MODE=C2: and no D1-H2 repair.

    MODE=NONE|C2 SHARD=i/n ONLY=<log> python3 k4/d1/core4_smt_e1.py [max_junk]
"""
import sys, os, itertools, collections, time, json
import z3

MODE = os.environ.get('MODE', 'NONE')


def enum(max_junk):
    out = set()
    # optional pick relevances: k~1,2,3 ; x~2,3 ; z~0,3 ; w~0,2
    opts = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 0), (2, 3), (3, 0), (3, 2)]
    masks = [mk for mk in range(1, 16) if not mk & 2]               # junk valued by subsets of {0, 2, 3}
    for sel in itertools.product((0, 1), repeat=len(opts)):
        base = [{0}, {0, 1}, {1, 2}, {1, 3}]
        for (i, g), f in zip(opts, sel):
            if f: base[i].add(g)
        if any(len(b) > 4 for b in base): continue
        for nj in range(1, max_junk + 1):
            for combo in itertools.combinations_with_replacement(masks, nj):
                R = [set(b) for b in base]
                for t, mk in enumerate(combo):
                    for i in range(4):
                        if mk >> i & 1: R[i].add(4 + t)
                if any(len(r) > 4 for r in R): continue
                if not any(mk & 1 for mk in combo): continue
                for f2 in ((0, 1) if 0 in R[2] else (0,)):
                    for f3 in ((0, 1) if 0 in R[3] else (0,)):
                        key = (sel, combo, f2, f3)
                        if key in out: continue
                        out.add(key)
                        yield [sorted(r) for r in R], list(range(4, 4 + nj)), (f2, f3)


def build(R, J, flags):
    n = 4
    val = {}
    for i in range(n):
        for g in R[i]: val[(i, g)] = z3.Real('u%d_%d' % (i, g))
    def vv(i, g): return val.get((i, g), z3.RealVal(0))
    def tot(i, S): return z3.Sum([vv(i, g) for g in S] + [z3.RealVal(0)])
    s = z3.Solver()
    for key in val: s.add(val[key] > 0)
    order = [0, 1, 2, 3]; taken = []
    for i in order:
        for g in R[i]:
            if g == i or g in taken: continue
            s.add(z3.Or(vv(i, i) > vv(i, g), z3.And(vv(i, i) == vv(i, g), i < g)))
        taken.append(i)
    P = [vv(i, i) for i in range(n)]
    def threatens(i, ti, X):
        if len(X) < 2: return z3.BoolVal(False)
        vals = [vv(i, g) for g in X]
        return z3.Or([z3.Sum(vals) - vals[t] > ti for t in range(len(vals))])
    def efx(X):
        c = []
        for j in range(n):
            for i in range(n):
                if i != j: c.append(z3.Not(threatens(i, tot(i, X[i]), X[j])))
        return z3.And(c)
    def unfrozen(i, B):
        if len(B[i]) != 1: return z3.BoolVal(True)
        g = B[i][0]
        return z3.And([vv(j, g) <= tot(j, B[j]) for j in range(n) if j != i])
    B0 = [[0], [1], [2], [3]]
    s.add(vv(1, 0) > P[1], vv(2, 1) > P[2], vv(3, 1) > P[3])
    s.add(unfrozen(2, B0), unfrozen(3, B0))
    for i, f in ((2, flags[0]), (3, flags[1])):
        if 0 in R[i]: s.add(vv(i, 0) > P[i] if f else vv(i, 0) <= P[i])
    chains = [(0, 1, 2), (0, 1, 3)]
    if flags[0]: chains.append((0, 2))
    if flags[1]: chains.append((0, 3))
    def after(path, H0):
        B = [list(b) for b in B0]
        for t in range(1, len(path)): B[path[t]] = [path[t - 1]]
        B[0] = list(H0)
        return B
    for path in chains:
        u, pred = path[-1], path[-2]
        Pi = J + [u]
        B = after(path, [g for g in Pi if g in R[0]])
        s.add(z3.Not(unfrozen(u, B)), threatens(u, vv(u, pred), Pi))
    # hard
    for o in range(n):
        rest = [i for i in range(n) if i != o]
        for r in range(0, len(rest) + 1):
            for who in itertools.combinations(rest, r):
                for gs in itertools.permutations(J, r):
                    X = [list(b) for b in B0]
                    for i, g in zip(who, gs): X[i] = X[i] + [g]
                    X[o] = X[o] + [g for g in J if g not in gs]
                    s.add(z3.Not(efx(X)))
    if MODE == 'C2':
        def sstar_none(B, L):
            alts = []
            cand = [1, 2, 3]
            for r in range(0, 4):
                for who in itertools.combinations(cand, r):
                    for gs in itertools.permutations(L, r):
                        X = [list(b) for b in B]
                        conds = []
                        for i, g in zip(who, gs):
                            X[i] = X[i] + [g]
                            conds.append(z3.BoolVal(len(B[i]) <= 1)); conds.append(unfrozen(i, B))
                        X[0] = X[0] + [g for g in L if g not in gs]
                        alts.append(z3.And(conds + [efx(X)]))
            return z3.Not(z3.Or(alts))
        def minimal(H0):
            return z3.And([tot(0, H0) > P[0]] + [tot(0, [h for h in H0 if h != e]) <= P[0] for e in H0])
        wanters = {1: [2, 3], 0: [1] + [i for i, f in ((2, flags[0]), (3, flags[1])) if f]}
        for path in chains:
            u, pred = path[-1], path[-2]
            exts = [None]
            for u2 in wanters[pred]:
                if u2 in path or u2 == 1: continue
                for r in (0, 1, 2):
                    for S in itertools.combinations(J, r): exts.append((u2, S))
            for ext in exts:
                if ext is None: Pi = J + [u]; c0 = z3.BoolVal(True)
                else: Pi = [g for g in J if g not in ext[1]] + [ext[0]]; c0 = tot(ext[0], [u] + list(ext[1])) > P[ext[0]]
                kp = [g for g in Pi if g in R[0]]
                for r in range(1, len(kp) + 1):
                    for H0 in itertools.combinations(kp, r):
                        B = after(path, list(H0))
                        if ext is not None: B[ext[0]] = [u] + list(ext[1])
                        L = [g for g in Pi if g not in H0]
                        s.add(z3.Implies(z3.And(minimal(list(H0)), c0), sstar_none(B, L)))
    return s


if __name__ == '__main__':
    maxj = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    print('$ MODE=%s SHARD=%s python3 k4/d1/core4_smt_e1.py' % (MODE, os.environ.get('SHARD')), *sys.argv[1:], flush=True)
    only = None
    if os.environ.get('ONLY'):
        only = set()
        for line in open(os.environ['ONLY']):
            if line.startswith('SAT'):
                R_, e = json.JSONDecoder().raw_decode(line[4:]); only.add(json.dumps(R_) + ' ' + line.split(' wants0 ')[1].strip())
    C = collections.Counter(); t0 = time.time(); shard = os.environ.get('SHARD')
    for idx, (R, J, fl) in enumerate(enum(maxj)):
        if shard:
            a, b = map(int, shard.split('/'))
            if idx % b != a: continue
        if only is not None and json.dumps(R) + ' ' + str(fl) not in only: continue
        s = build(R, J, fl); r = s.check(); C['structures'] += 1; C[str(r)] += 1
        if r == z3.sat: print('SAT', json.dumps(R), 'wants0', fl, flush=True)
    for kk in sorted(C): print(kk, C[kk])
    print('time %.0f s' % (time.time() - t0))
