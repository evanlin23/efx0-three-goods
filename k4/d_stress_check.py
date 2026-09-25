"""Second, independently written SAT encoding for k4/d_stress.py (the repository rule for UNSAT claims): does an EFX0
allocation with at most `big` bundles of more than `s` goods exist, for FIXED integer values? Written from scratch
(pysat): x[g][j] = good g to agent j (exactly one owner); size indicators via cardinality constraints; EFX0 as
forbidden patterns derived directly from v_i(X_i) >= v_i(X_j) - v_i(g) for every g in X_j, with an indicator for "X_j
holds a good outside R_i". Every allocation found is re-checked by raw() (the plain definition).
Usage: d_stress_check.py FILE.json.gz [--decide]   (a witness file written by d_stress.py --witnesses): checks every
       profile is a strict core profile (each agent's values one type of search4.domain) and re-checks every allocation
       by raw() and the D2 shape; with --decide also decides every profile with this encoding (D2 must be satisfiable).
       Exits nonzero on any failure.
       d_stress_check.py --selftest FAMILY ARGS N   (N random profiles of a d_stress family, both encodings; the
       "all bundles <= 2" comparison is skipped when m > 2n, where both are unsatisfiable by counting and the SAT
       calls are pigeonhole-hard)"""
import sys, json, itertools, random, gzip
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

SOLVER = 'cadical153'   # glucose4 takes minutes on some tree and cycle profiles that CaDiCaL solves in 0.1 s


def raw(sets, values, A):
    n, m = len(sets), len(A)
    v = [dict(zip(S, vals)) for S, vals in zip(sets, values)]
    bund = [[g for g in range(m) if A[g] == j] for j in range(n)]
    for i in range(n):
        mine = sum(v[i].get(g, 0) for g in bund[i])
        for j in range(n):
            if j == i: continue
            tot = sum(v[i].get(g, 0) for g in bund[j])
            if any(tot - v[i].get(g, 0) > mine for g in bund[j]): return False
    return True


def encode(sets, values, s=2, big=1):
    """Clauses of the model, the x variables, and the big_j indicators (None if s is None)."""
    n = len(sets)
    m = max(g for S in sets for g in S) + 1
    vp = IDPool()
    x = [[vp.id(('x', g, j)) for j in range(n)] for g in range(m)]
    cl = []
    for g in range(m):
        cl.append(x[g])
        cl += [[-x[g][a], -x[g][b]] for a in range(n) for b in range(a + 1, n)]
    bigv = None
    if s is not None:
        bigv = [vp.id(('big', j)) for j in range(n)]
        for j in range(n):
            # sum_g x[g][j] <= s unless big_j: at most m of {x[g][j]} together with (m - s) copies of not-big_j
            cp = [vp.id(('nb', j, k)) for k in range(m - s)]
            for c in cp: cl += [[c, bigv[j]], [-c, -bigv[j]]]
            cl += CardEnc.atmost(lits=[x[g][j] for g in range(m)] + cp, bound=m, vpool=vp, encoding=EncType.seqcounter).clauses
        cl += CardEnc.atmost(lits=bigv, bound=big, vpool=vp, encoding=EncType.seqcounter).clauses
    for i, S in enumerate(sets):
        val = dict(zip(S, values[i]))
        Sset = set(S)
        for j in range(n):
            if j == i: continue
            out = vp.id(('out', i, j))                       # X_j holds a good outside R_i
            cl += [[-x[g][j], out] for g in range(m) if g not in Sset]   # any outside good forces out
            for r in range(len(S) + 1):
                for O in itertools.combinations(S, r):
                    vo = sum(val[g] for g in O)
                    rest = [g for g in S if g not in O]
                    own = [-x[g][i] for g in O] + [x[g][i] for g in rest]   # negation of "X_i ∩ R_i = O"
                    for q in range(1, len(rest) + 1):
                        for T in itertools.combinations(rest, q):
                            vt = sum(val[g] for g in T)
                            lo = vt - min(val[g] for g in T)
                            sel = [-x[g][j] for g in T] + [x[g][j] for g in rest if g not in T]
                            if vo < lo and len(T) >= 2:      # unsafe even if X_j ⊆ R_i (threat v(T) - min)
                                cl.append(own + sel)
                            elif vo < vt:                    # unsafe if X_j also holds a good outside R_i
                                cl.append(own + sel + [-out])
    return cl, x, bigv, n, m


def _alloc(sol, x, n, m):
    mod = set(l for l in sol.get_model() if l > 0)
    return [next(j for j in range(n) if x[g][j] in mod) for g in range(m)]


def decide(sets, values, s=2, big=1):
    cl, x, bigv, n, m = encode(sets, values, s, big)
    with Solver(name=SOLVER, bootstrap_with=cl) as sol:
        if not sol.solve(): return None
        A = _alloc(sol, x, n, m)
        assert raw(sets, values, A), 'encoding produced a non-EFX0 allocation'
        if s is not None:
            assert sum(1 for j in range(n) if A.count(j) > s) <= big
        return A


def owners(sets, values):
    """The agents o for which a D2 EFX0 allocation exists in which no bundle other than o's has more than 2 goods."""
    cl, x, bigv, n, m = encode(sets, values, 2, 1)
    out = []
    with Solver(name=SOLVER, bootstrap_with=cl) as sol:
        for o in range(n):
            if sol.solve(assumptions=[-bigv[j] for j in range(n) if j != o]):
                A = _alloc(sol, x, n, m)
                assert raw(sets, values, A) and all(A.count(j) <= 2 for j in range(n) if j != o)
                out.append(o)
    return out


def main():
    import d_stress as D
    print('commit %s' % D.git_head(), flush=True)
    if sys.argv[1] == '--selftest':
        fam, *rest = sys.argv[2:-1]
        N = int(sys.argv[-1])
        rng = random.Random(5)
        I = D.Inst(D.build([fam] + rest, rng))
        pigeon = I.m > 2 * I.n                                 # all bundles <= 2 impossible by counting
        agree = nc2 = 0
        for k in range(N):
            p = I.random_profile(rng)
            a, b = I.shape(p) is not None, decide(I.sets, I.values(p)) is not None
            if pigeon: c = d = False
            else: c, d = I.shape(p, 2, 0) is not None, decide(I.sets, I.values(p), 2, 0) is not None   # all bundles <= 2
            agree += (a == b) and (c == d)
            nc2 += not c
            if a != b or c != d: print('DISAGREE', json.dumps(I.values(p)))
        print('selftest %s: %d of %d profiles decided alike (d_stress.py vs this encoding), for D2 and for all bundles <= 2 '
              '(the latter unsatisfiable in %d%s)' % (' '.join([fam] + rest), agree, N, nc2,
                                                       '; not run: m > 2n, unsatisfiable by counting' if pigeon else ''))
        sys.exit(0 if agree == N else 1)
    rec = json.load(gzip.open(sys.argv[1], 'rt'))
    I = D.Inst(rec['sets'])
    bad = dec = 0
    for vals, A in rec['witnesses']:
        ok = all(any(list(t) == v for t in I.dom[i]) for i, v in enumerate(vals))      # a strict core profile
        ok = ok and len(A) == I.m and raw(I.sets, vals, A) and sum(1 for j in range(I.n) if A.count(j) > 2) <= 1
        if ok and '--decide' in sys.argv:
            ok = decide(I.sets, vals) is not None
            dec += 1
        bad += not ok
        if not ok: print('FAIL', json.dumps(vals), json.dumps(A))
    print('%s (%s): %d witnesses; %d failures of the domain, raw EFX0 and D2-shape checks%s' % (
        sys.argv[1], ' '.join(rec['args']), len(rec['witnesses']), bad,
        '; %d profiles also decided D2-satisfiable by this encoding' % dec if dec else ''), flush=True)
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
