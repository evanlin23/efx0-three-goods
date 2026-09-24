"""Plan Step 2: the structure of the large bundle.
  c2    For every connected core with n agents and m goods: the ranking profiles with no EFX0 allocation whose bundles
        all have <= 2 goods ("C2-failing"; CEGAR over profiles: a covered profile is excluded by the raw safety masks of
        the allocation found, a failing one by a blocking clause; the inner model is frontier.build(..., 'C2')).
  structure
        For every C2-failing (core, profile): ALL EFX0 allocations with exactly one bundle of >= 3 goods (the large
        bundle L, owner o) and all others <= 2 (SAT enumeration with blocking clauses; each solution re-checked with
        construct.raw_ok). Reports, per (n, m): the minimum size of L; which L5 cases the owner can use; whether L
        can consist of the owner's top plus goods that are private to agents who hold their own tops; the exceptions.
  relate
        For EVERY profile: contested tops (goods that are the top of >= 2 agents), P-capacity p (the most contested
        tops that can be fixed at once by case P: a winner holds the top, every other claimant holds its bottom pair,
        all these pairs disjoint), deficit delta = #contested - p, slack sigma = 2n - m. Lemma (proofs/construction.md):
        an allocation with all bundles <= 2 needs delta <= sigma. Tabulates C2 failure against delta - sigma, and
        compares with construction LB (construct.py), which uses a large bundle iff |NA| > sigma after its upgrades.
Usage: large_bundle.py c2|structure|relate n m [m ...] [--jobs=N]"""
import sys, os, itertools, collections, time, multiprocessing
from pysat.solvers import Glucose4
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from frontier import build, raw_masks, options
from cores_nauty import gen_cores_nauty
from construct import raw_ok, construct, phase1, phase2
PERMS = list(itertools.permutations(range(3)))

def ranked(sets, prof):
    return [tuple(S[p] for p in PERMS[k]) for S, k in zip(sets, prof)]

def c2_failing(n, m, sets):
    inner, sel, x = build(n, m, [tuple(S) for S in sets], 'C2')
    pool = IDPool(); r = [[pool.id(('r', i, k)) for k in range(6)] for i in range(n)]
    outer = Glucose4()
    for i in range(n):
        for cl in CardEnc.equals(r[i], 1, vpool=pool, encoding=EncType.pairwise).clauses: outer.add_clause(cl)
    fails = []
    while outer.solve():
        mdl = set(l for l in outer.get_model() if l > 0)
        prof = [next(k for k in range(6) if r[i][k] in mdl) for i in range(n)]
        if not inner.solve(assumptions=[sel[(i, prof[i])] for i in range(n)]):
            fails.append(tuple(prof)); outer.add_clause([-r[i][prof[i]] for i in range(n)]); continue
        imdl = set(l for l in inner.get_model() if l > 0)
        X = [next(j for j in range(n) if x(g, j) in imdl) for g in range(m)]
        M = raw_masks(n, m, [tuple(S) for S in sets], X)
        assert all(M[i, prof[i]] for i in range(n))
        outer.add_clause([r[i][k] for i in range(n) for k in range(6) if not M[i, k]])
    inner.delete(); outer.delete()
    return sorted(fails)

def c2_failing_brute(n, m, sets):
    """Second, SAT-free computation of c2_failing: enumerate every allocation whose bundles all have <= 2 goods, compute
    for each agent the rankings under which it is safe (raw definition, construct.raw_ok on the one-agent test), and
    take the union of the covered profile boxes. Feasible for n <= 4."""
    import numpy as np
    cov = np.zeros((6,) * n, dtype=bool)
    for X in itertools.product(range(n), repeat=m):
        if max(collections.Counter(X).values()) > 2: continue
        masks = []
        for i in range(n):
            mk = []
            for k in range(6):
                trip = [tuple(S) for S in sets]; trip[i] = tuple(sets[i][p] for p in PERMS[k])
                mk.append(agent_safe_raw(n, m, trip, X, i))
            masks.append(np.flatnonzero(mk))
        cov[np.ix_(*masks)] = True
    return sorted(tuple(int(v) for v in p) for p in zip(*np.nonzero(~cov)))

def agent_safe_raw(n, m, trip, X, i):
    """Raw EFX0 test for agent i alone (three balanced realizations, which must agree)."""
    bundles = [[g for g in range(m) if X[g] == j] for j in range(n)]; res = set()
    for vals in ((4, 3, 2), (10, 9, 2), (10, 6, 5)):
        v = dict(zip(trip[i], vals)); own = sum(v.get(g, 0) for g in bundles[i])
        res.add(all(sum(w) - min(w) <= own for j, B in enumerate(bundles) if j != i and len(B) >= 2
                    for w in [[v.get(g, 0) for g in B]]))
    if len(res) != 1: raise SystemExit("realizations disagree")
    return res.pop()

def one_large(n, m, trip):
    """All allocations with exactly one bundle of >= 3 goods, the others <= 2, every agent safe (L5 cases)."""
    pool = IDPool(); x = lambda g, j: pool.id(('x', g, j)); s = lambda g: pool.id(('s', g))
    big = [pool.id(('big', j)) for j in range(n)]; cls = []
    for g in range(m): cls += CardEnc.equals([x(g, j) for j in range(n)], 1, vpool=pool, encoding=EncType.pairwise).clauses
    for g in range(m):
        for j in range(n):
            for h in range(m):
                if h != g: cls.append([-s(g), -x(g, j), -x(h, j)])
    for j in range(n):
        for g, h, k in itertools.combinations(range(m), 3): cls.append([big[j], -x(g, j), -x(h, j), -x(k, j)])
        cls += [[-big[j]] + c for c in CardEnc.atleast([x(g, j) for g in range(m)], 3, vpool=pool, encoding=EncType.seqcounter).clauses]
    cls += CardEnc.equals(big, 1, vpool=pool, encoding=EncType.pairwise).clauses
    for i, (a, b, c) in enumerate(trip):
        opts = []
        for tag, conds in (('T1', [x(a, i), x(b, i)]), ('T2', [x(a, i), x(c, i)]), ('P', [x(b, i), x(c, i)]),
                           ('B', [x(b, i), s(a)]), ('C', [x(c, i), s(a), s(b)]), ('E', [s(a), s(b), s(c)])):
            y = pool.id((tag, i)); cls += [[-y, l] for l in conds]; opts.append(y)
        y = pool.id(('T3', i)); cls.append([-y, x(a, i)]); opts.append(y)
        for j in range(n):
            for h in range(m):
                if h not in (b, c): cls.append([-y, -x(b, j), -x(c, j), -x(h, j)])
        cls.append(opts)
    S = Glucose4(bootstrap_with=cls); out = []
    while S.solve():
        mdl = set(l for l in S.get_model() if l > 0)
        X = [next(j for j in range(n) if x(g, j) in mdl) for g in range(m)]
        if not raw_ok(n, m, trip, X): raise SystemExit(f"model/definition mismatch: {trip} {X}")
        out.append(X); S.add_clause([-x(g, X[g]) for g in range(m)])
    S.delete(); return out

def case_of(i, trip, X, size):
    a, b, c = trip[i]; alone = lambda g: size[X[g]] == 1
    if X[a] == i: return 'T'
    if X[b] == i and X[c] == i: return 'P'
    if X[b] == i and alone(a): return 'B'
    if X[c] == i and alone(a) and alone(b): return 'C'
    return 'E'

def features(n, m, sets, trip, X):
    size = collections.Counter(X); o = next(j for j, v in size.items() if v >= 3)
    L = [g for g in range(m) if X[g] == o]
    deg = collections.Counter(g for S in sets for g in S)
    cases = [case_of(i, trip, X, size) for i in range(n)]
    other = [g for g in L if g not in trip[o]]
    holders = [k for g in other for k in range(n) if g in trip[k]]
    return {'D': len(L), 'owner_case': cases[o], 'owner_top': X[trip[o][0]] == o,
            'own': ''.join('abc'[trip[o].index(g)] for g in sorted((g for g in L if g in trip[o]), key=trip[o].index)),
            'private': all(deg[g] == 1 for g in other),
            'holders_top': all(X[trip[k][0]] == k for k in holders),
            'holders_TB': all(cases[k] in 'TB' for k in holders)}

def structure(task):
    n, m, sets = task; out = []
    for prof in c2_failing(n, m, sets):
        trip = ranked(sets, prof)
        out.append((prof, [features(n, m, sets, trip, X) for X in one_large(n, m, trip)]))
    return sets, out

def p_capacity(trip):
    claim = collections.defaultdict(list)
    for i, t in enumerate(trip): claim[t[0]].append(i)
    C = [g for g in claim if len(claim[g]) >= 2]
    best = 0
    for F in range(len(C), 0, -1):
        for sub in itertools.combinations(C, F):
            for winners in itertools.product(*(claim[g] for g in sub)):
                pairs = [frozenset(trip[i][1:]) for g, w in zip(sub, winners) for i in claim[g] if i != w]
                if len(set().union(*pairs)) == 2 * len(pairs): return len(C), n - len(claim), F
    return len(C), n - len(claim), best

def na_split(n, m, trip):
    """LB's goods needed alone after its upgrades, split into tops (a_k of some needing agent k) and the rest."""
    Y, J = phase1(n, m, trip); res = phase2(n, m, trip, Y, J); up = res[2]
    rank = [{g: r for r, g in enumerate(t)} for t in trip]
    need = [(k, r) for k in range(n) if k not in up for r in range(rank[k][Y[k]] if Y[k] is not None else 3)]
    tops = {trip[k][0] for k, r in need}
    return len(tops), len({trip[k][r] for k, r in need} - tops)

def relate(task):
    n, m, sets = task; fails = set(c2_failing(n, m, sets)); tab = collections.Counter()
    for prof in itertools.product(range(6), repeat=n):
        trip = ranked(sets, prof); nc, kappa, p = p_capacity(trip)
        X = construct(n, m, trip); big = max(collections.Counter(X).values()) >= 3
        tab[(nc - p - (2 * n - m), prof in fails, big)] += 1
        nt, nl = na_split(n, m, trip)
        tab[('NA', nt - (2 * n - m), nl, prof in fails)] += 1
        if big:
            f = features(n, m, sets, trip, X)
            tab[('LB owner case', f['owner_case'])] += 1
            tab[('LB rest', 'private goods of agents holding their tops' if f['private'] and f['holders_top'] else
                 'private goods, some agent not holding its top' if f['private'] else 'contains a shared good')] += 1
    return tab

if __name__ == '__main__':
    mode = sys.argv[1]; args, opts = options(sys.argv[2:]); n, ms = args[0], args[1:]
    jobs = int(opts.get('jobs', os.cpu_count())); t0 = time.time()
    with multiprocessing.Pool(jobs) as pool:
        for m in ms:
            cores = [(n, m, s) for _, s in gen_cores_nauty(n, m)]
            if mode == 'c2':
                res = pool.starmap(c2_failing, cores, chunksize=1)
                msg = (f"n={n} m={m}: {len(cores)} cores; C2-failing: {sum(map(bool, res))} cores, "
                       f"{sum(map(len, res))} of {len(cores) * 6 ** n} (core, profile) pairs")
                if 'brute' in opts:
                    res2 = pool.starmap(c2_failing_brute, cores, chunksize=1)
                    msg += f"; brute force (SAT-free) agrees on {sum(a == b for a, b in zip(res, res2))} of {len(cores)} cores"
                print(msg + f"  [{time.time() - t0:.0f}s]", flush=True)
                for (_, _, sets), F in zip(cores, res):
                    if F and 'list' in opts: print(f"   {sets}: {len(F)} profiles, first {F[0]}: (a, b, c) {ranked(sets, F[0])}")
            elif mode == 'structure':
                npairs = 0; minD = collections.Counter(); cases = collections.Counter(); some = collections.Counter()
                nsol = []; exc = []; big4 = []
                for sets, out in pool.imap_unordered(structure, cores, chunksize=1):
                    for prof, fs in out:
                        npairs += 1; nsol.append(len(fs)); minD[min(f['D'] for f in fs)] += 1
                        if min(f['D'] for f in fs) >= 4: big4.append((sets, prof))
                        for c in {f['owner_case'] for f in fs}: cases[c] += 1
                        tests = {'owner holds its top': lambda f: f['owner_top'],
                                 'L minus owner goods all private': lambda f: f['private'],
                                 '... and their agents hold their tops': lambda f: f['private'] and f['holders_top'],
                                 'owner holds top, rest private, their agents hold tops':
                                     lambda f: f['owner_top'] and f['private'] and f['holders_top'],
                                 'rest private, their agents in case T or B': lambda f: f['private'] and f['holders_TB'],
                                 'owner in case C, rest private, their agents in case T or B':
                                     lambda f: f['owner_case'] == 'C' and f['private'] and f['holders_TB'],
                                 'L = owner\'s c + private goods of agents in case T or B':
                                     lambda f: f['own'] == 'c' and f['private'] and f['holders_TB']}
                        for k, t in tests.items():
                            if any(t(f) for f in fs): some[k] += 1
                        if not any(tests['owner holds top, rest private, their agents hold tops'](f) for f in fs):
                            exc.append((sets, prof, ranked(sets, prof)))
                print(f"n={n} m={m}: {npairs} C2-failing (core, profile) pairs; one-large-bundle allocations per pair: "
                      f"min {min(nsol, default=0)}, max {max(nsol, default=0)}  [{time.time() - t0:.0f}s]")
                print(f"  minimum size of the large bundle: {dict(sorted(minD.items()))}")
                print(f"  pairs where the owner can use case: {dict(sorted(cases.items()))}")
                if big4: print(f"  pairs needing a large bundle of >= 4 goods: {len(big4)}, in {len({str(s) for s, _ in big4})} cores")
                for sets, prof in big4: print(f"    {sets} profile {prof}: (a, b, c) {ranked(sets, prof)}")
                for k, v in some.items(): print(f"  some solution has [{k}]: {v} of {npairs}")
                print(f"  pairs where no solution has [owner holds top, rest private, their agents hold tops]: {len(exc)}")
                for sets, prof, trip in exc[:5]: print(f"    e.g. {sets} profile {prof}, (a, b, c): {trip}")
            elif mode == 'relate':
                tab = collections.Counter()
                for t in pool.imap_unordered(relate, cores, chunksize=1): tab.update(t)
                print(f"n={n} m={m} (sigma = {2 * n - m}), all {len(cores) * 6 ** n} (core, profile) pairs  [{time.time() - t0:.0f}s]")
                print("  delta - sigma | pairs | C2 fails | LB uses a large bundle | of those, C2 fails")
                for d in sorted({k[0] for k in tab if isinstance(k[0], int)}):
                    tot = sum(v for k, v in tab.items() if k[0] == d)
                    f = sum(v for k, v in tab.items() if k[0] == d and k[1])
                    b = sum(v for k, v in tab.items() if k[0] == d and k[2])
                    bf = sum(v for k, v in tab.items() if k[0] == d and k[1] and k[2])
                    print(f"  {d:13d} | {tot:9d} | {f:8d} | {b:8d} | {bf:8d}")
                print("  LB's needed-alone goods: tops T and lower goods L; T - sigma | L | pairs | C2 fails")
                for t_, l_ in sorted({k[1:3] for k in tab if k[0] == 'NA'}):
                    tot = tab[('NA', t_, l_, False)] + tab[('NA', t_, l_, True)]
                    print(f"  {t_:10d} | {l_:3d} | {tot:9d} | {tab[('NA', t_, l_, True)]:8d}")
                print(f"  C2 fails but LB uses no large bundle (impossible): {sum(v for k, v in tab.items() if isinstance(k[0], int) and k[1] and not k[2])}")
                print(f"  LB's large bundle, owner's case: {dict(sorted((k[1], v) for k, v in tab.items() if k[0] == 'LB owner case'))}")
                print(f"  LB's large bundle minus the owner's goods: {dict(sorted((k[1], v) for k, v in tab.items() if k[0] == 'LB rest'))}")
