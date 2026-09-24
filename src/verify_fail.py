"""Independent confirmation that a C2 failure is real. For bundles <= 2, EFX0 is equivalent to:
   for every agent i and every good g outside X_i that sits in a 2-good bundle, v_i(g) <= v_i(X_i).
(Removing either good of a pair {g,h} leaves the other, so the requirement is max(v_i(g), v_i(h)) <= v_i(X_i).)
This encoding uses realized numbers and none of the T/P/B/C/E case analysis."""
import json, itertools, collections, time
from pysat.solvers import Minisat22
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from frontier import PERMS, build

def indep_c2(n, m, trip, vals=(2.0, 1.5, 1.0)):
    v = [dict(zip(t, vals)) for t in trip]
    pool = IDPool(); x = lambda g, j: pool.id(('x', g, j)); pr = lambda g: pool.id(('pr', g))
    cls = []
    for g in range(m): cls += CardEnc.equals(lits=[x(g, j) for j in range(n)], bound=1, vpool=pool, encoding=EncType.pairwise).clauses
    for j in range(n): cls += CardEnc.atmost(lits=[x(g, j) for g in range(m)], bound=2, vpool=pool, encoding=EncType.seqcounter).clauses
    for g in range(m):
        for j in range(n):
            for h in range(m):
                if h != g: cls.append([-x(g, j), -x(h, j), pr(g)])          # g paired => pr(g)
    for i in range(n):
        R = list(v[i])
        for g in R:
            # pr(g) and g not mine  =>  my bundle is worth >= v_i(g)
            ok = [x(g, i)] + [x(h, i) for h in R if h != g and v[i][h] >= v[i][g]]
            for h, h2 in itertools.combinations([h for h in R if h != g], 2):
                if v[i][h] + v[i][h2] >= v[i][g]:
                    y = pool.id(('both', i, h, h2)); cls += [[-y, x(h, i)], [-y, x(h2, i)]]; ok.append(y)
            cls.append([-pr(g)] + ok)
    with Minisat22(bootstrap_with=cls) as S: return S.solve()

R = json.load(open('frontier_results_5_6.json'))
fails = [r for r in R if r['n'] == 6 and r['m'] == 10 and r['modes']['C2']['status'] == 'FAIL']
agree = 0
for r in fails:
    trip = [tuple(S[p] for p in PERMS[k]) for S, k in zip(r['sets'], r['modes']['C2']['bad'])]
    if not indep_c2(6, 10, trip): agree += 1
print(f"[independent check] n=6 m=10 C2 failures confirmed UNSAT by second encoding: {agree}/{len(fails)}")
# failure density: how many of the 6^6 profiles fail C2, for three failing hypergraphs
for r in fails[:3]:
    Sv, sel, _ = build(6, 10, [tuple(S) for S in r['sets']], 'C2'); t0 = time.time(); bad = 0
    for prof in itertools.product(range(6), repeat=6):
        if not Sv.solve(assumptions=[sel[(i, prof[i])] for i in range(6)]): bad += 1
    Sv.delete()
    print(f"  hypergraph {r['sets']}: {bad}/46656 profiles fail C2 ({100*bad/46656:.2f}%)  [{time.time()-t0:.0f}s]")
# one explicit example: ranked triples and an allocation with one large bundle
r = min(fails, key=lambda r: sum(len(set(S)) for S in r['sets']))
trip = [tuple(S[p] for p in PERMS[k]) for S, k in zip(r['sets'], r['modes']['C2']['bad'])]
Sv, sel, x = build(6, 10, [tuple(S) for S in r['sets']], 'C3')
assert Sv.solve(assumptions=[sel[(i, k)] for i, k in enumerate(r['modes']['C2']['bad'])])
mdl = set(l for l in Sv.get_model() if l > 0)
X = [next(j for j in range(6) if x(g, j) in mdl) for g in range(10)]
print("  example (agent: a > b > c):", trip)
print("  EFX0 allocation with one large bundle:", [[g for g in range(10) if X[g] == j] for j in range(6)])

import sys
if agree != len(fails) or len(fails) != 57:
    print("MISMATCH: expected 57 refutations, all confirmed"); sys.exit(1)
