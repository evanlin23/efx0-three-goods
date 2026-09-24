"""Exhaustive check of every non-multigraph core with n=5 agents, m=9 goods.
Core: each agent has exactly 3 relevant goods, is balanced, has <= 1 private good; some good has degree >= 3.
Counting forces m=9 and pi (#private goods) in {4,5}. For each hypergraph (up to isomorphism) and each of the
6^5 orderings, decide: EFX0 with all bundles <= 2 (C2)? else with one dump bundle (C3)? else any EFX0 (general)?"""
import itertools, sys, time, json
from pysat.solvers import Minisat22
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

def reps_pi5():
    pairs = list(itertools.combinations(range(4), 2)); seen = {}
    for ch in itertools.product(pairs, repeat=5):
        deg = [0] * 4
        for p in ch:
            for g in p: deg[g] += 1
        if min(deg) < 2: continue
        key = min(tuple(sorted(tuple(sorted((pm[a], pm[b]))) for a, b in ch)) for pm in itertools.permutations(range(4)))
        seen[key] = 1
    out = []
    for key in seen:        # shared goods 0..3, private goods 4..8 (one per agent)
        out.append([tuple(p) + (4 + i,) for i, p in enumerate(key)])
    return out

def reps_pi4():
    pairs = list(itertools.combinations(range(5), 2)); trips = list(itertools.combinations(range(5), 3)); seen = {}
    perms = list(itertools.permutations(range(5)))
    for t in trips:
        for ch in itertools.product(pairs, repeat=4):
            deg = [0] * 5
            for g in t: deg[g] += 1
            for p in ch:
                for g in p: deg[g] += 1
            if min(deg) < 2: continue
            key = min((tuple(sorted(pm[g] for g in t)),) + tuple(sorted(tuple(sorted((pm[a], pm[b]))) for a, b in ch)) for pm in perms)
            seen[key] = 1
    out = []
    for key in seen:        # agent 0 has no private good; agents 1..4 have private goods 5..8
        out.append([key[0]] + [tuple(p) + (4 + i,) for i, p in enumerate(key[1:], start=1)])
    return out

def build(n, m, sets, mode):
    """mode 'C2' (bundles<=2), 'C3' (<=2 except one dump), 'G' (any). Returns solver, selector map."""
    pool = IDPool(); x = lambda g, j: pool.id(('x', g, j)); s = lambda g: pool.id(('s', g))
    cls = []
    for g in range(m):
        cls += CardEnc.equals(lits=[x(g, j) for j in range(n)], bound=1, vpool=pool, encoding=EncType.pairwise).clauses
    for g in range(m):
        for j in range(n):
            for h in range(m):
                if h != g: cls.append([-s(g), -x(g, j), -x(h, j)])
    if mode == 'C2':
        for j in range(n):
            cls += CardEnc.atmost(lits=[x(g, j) for g in range(m)], bound=2, vpool=pool, encoding=EncType.seqcounter).clauses
    if mode == 'C3':
        big = [pool.id(('big', j)) for j in range(n)]
        for j in range(n):
            for g, h, k in itertools.combinations(range(m), 3):
                cls.append([big[j], -x(g, j), -x(h, j), -x(k, j)])
        cls += CardEnc.atmost(lits=big, bound=1, vpool=pool, encoding=EncType.pairwise).clauses
    sel = {}
    for i, S in enumerate(sets):
        for a in S:
            b, c = [g for g in S if g != a]
            yT = pool.id(('Ta2', i, a)); cls += [[-yT, x(a, i)], [-yT, x(b, i), x(c, i)]]
            y3 = pool.id(('T3', i, a)); cls.append([-y3, x(a, i)])
            for j in range(n):
                for h in range(m):
                    if h not in (b, c): cls.append([-y3, -x(b, j), -x(c, j), -x(h, j)])
            yP = pool.id(('P', i, a)); cls += [[-yP, x(b, i)], [-yP, x(c, i)]]
        for (a, b) in itertools.permutations(S, 2):
            yB = pool.id(('B', i, b, a)); cls += [[-yB, x(b, i)], [-yB, s(a)]]
        for c in S:
            a, b = [g for g in S if g != c]
            yC = pool.id(('C', i, c)); cls += [[-yC, x(c, i)], [-yC, s(a)], [-yC, s(b)]]
        yE = pool.id(('E', i)); cls += [[-yE, s(g)] for g in S]
        for (a, b, c) in itertools.permutations(S):
            z = pool.id(('z', i, a, b, c)); sel[(i, a, b, c)] = z
            cls.append([-z, pool.id(('Ta2', i, a)), pool.id(('T3', i, a)), pool.id(('P', i, a)),
                        pool.id(('B', i, b, a)), pool.id(('C', i, c)), pool.id(('E', i))])
    S = Minisat22(bootstrap_with=cls)
    return S, sel, x

if __name__ == "__main__":
    t0 = time.time()
    R5, R4 = reps_pi5(), reps_pi4()
    print(f"hypergraphs up to isomorphism: pi=5: {len(R5)}, pi=4: {len(R4)}  ({time.time()-t0:.0f}s)", flush=True)
    n, m = 5, 9
    stats = {'profiles': 0, 'C2': 0, 'C3only': 0, 'Gonly': 0, 'none': 0}
    hard = []
    for hid, sets in enumerate(R5 + R4):
        solvers = {md: build(n, m, sets, md) for md in ('C2', 'C3', 'G')}
        for prof in itertools.product(*[list(itertools.permutations(S)) for S in sets]):
            stats['profiles'] += 1
            ok = None
            for md in ('C2', 'C3', 'G'):
                Sv, sel, _ = solvers[md]
                if Sv.solve(assumptions=[sel[(i,) + prof[i]] for i in range(n)]): ok = md; break
            if ok == 'C2': stats['C2'] += 1
            elif ok == 'C3': stats['C3only'] += 1
            elif ok == 'G': stats['Gonly'] += 1; hard.append((sets, prof))
            else: stats['none'] += 1; hard.append((sets, prof)); print("NO EFX0:", sets, prof, flush=True)
        for md in solvers: solvers[md][0].delete()
        if hid % 20 == 0:
            print(f"hypergraph {hid+1}/{len(R5)+len(R4)}: {stats} ({time.time()-t0:.0f}s)", flush=True)
    print("FINAL", stats, f"({time.time()-t0:.0f}s)", flush=True)
    json.dump({'stats': stats, 'hard': hard[:50]}, open('exhaust5_result.json', 'w'))
