"""Which PROVED mechanism gives OC1 at the sigma-optimal starts? (k4/rkmax.md §5)

For each sigma-optimal maximum matching Y (perfect starts only; others are counted):
  T0  : some receiver z has Theta(z) = {} (no dangerous agent threatened by J + Y_z at its pick value); then the picks
        have an S* completion owned by z (k4/oc1max_multi.md §2, Prop. T0 with Lemma 2 of k4/oc1_hall.md §4);
  S*  : otherwise, the picks have an S* completion with some owner (mmlib.sstar; Lemma 2 is its exact criterion);
  P1  : otherwise, the picks have some one-absorber completion (rklib);
  US  : otherwise, Theorem U or S (refereed CORRECT; relaxed form, h in J + {Y_z}) applies: theorem_s.s_cases yields a
        case, and its allocation is EFX0 (re-checked raw here);
  M   : otherwise, one official move repairs (rklib);
  F   : OC1 fails (a counterexample to RKMAX).
Data: the n = 4 export profiles (default) or random strict connected MC2-class cores (RAND=N n SEED).
    python3 rk_classes.py [STRIDE]              # n = 4 export
    python3 rk_classes.py rand N n SEED         # random cores, every sigma-optimal vector"""
import sys, os, gzip, json, collections, time, random, multiprocessing as mp
from rklib import Prof, lexmax
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.join(HERE, '..', '..')
sys.path.insert(0, os.path.join(ROOT, 'k4', 'oc1max_multi')); sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
import mmlib                                    # noqa: E402
from theorem_s import s_cases                   # noqa: E402


def theta(P, Y, ro, z):
    W = list(ro['J']) + [Y[z]]
    return [d for d in ro['D'] if P.threat(d, P.val[d][Y[d]], W)]


def classify_fast(sets, vals, Y, P=None):
    """Proved mechanisms first (cheap): T0, Theorem U/S, Lemma RF-B; then the picks' completion ('P', not hard),
    then 'M' (one official move, a gap of HS-MAX) or 'F' (RKMAX fails if Y is sigma-optimal)."""
    P = P or Prof(sets, vals); I = mmlib.Inst(sets, vals, m=P.m)
    ro = P.roles(Y)
    if any(g is None for g in Y): return 'nonperfect', ro
    if any(not theta(P, Y, ro, z) for z in ro['U']): return 'T0', ro
    base = mmlib.base_from_picks(Y); D = mmlib.dangerous(I, base)
    for k, Pch, h, H0, X, how in s_cases(I, base, D, relaxed=True, pick_too=True):
        if X is not None:
            assert P.efx0(X), ('Theorem S allocation not EFX0', sets, vals, Y)
            return 'US', ro
    if rfb_cases(P, Y, ro): return 'RFB', ro
    if P.one_absorber([frozenset([g]) for g in Y]) is not None: return 'P', ro
    r = P.oc1(Y)
    return ('GAP-M' if r == 'M' else 'F'), ro


def classify(sets, vals, Y, P=None):
    P = P or Prof(sets, vals); I = mmlib.Inst(sets, vals, m=P.m)
    ro = P.roles(Y)
    if any(g is None for g in Y): return 'nonperfect', ro
    if any(not theta(P, Y, ro, z) for z in ro['U']): return 'T0', ro
    base = mmlib.base_from_picks(Y)
    if mmlib.sstar_owners(I, base): return 'S*', ro
    B = [frozenset([g]) for g in Y]
    if P.one_absorber(B) is not None: return 'P1', ro
    D = mmlib.dangerous(I, base)
    for k, Pch, h, H0, X, how in s_cases(I, base, D, relaxed=True, pick_too=True):
        if X is not None:
            assert P.efx0(X), ('Theorem S allocation not EFX0', sets, vals, Y)
            return 'US', ro
    if rfb_cases(P, Y, ro): return 'RFB', ro
    r = P.oc1(Y)
    return ('M' if r == 'M' else 'F'), ro


def rfb_cases(P, Y, ro):
    """Lemma RF-B (k4/oc1_hall.md §24.8, refereed CORRECT): agents d != k, S subset of J with
    (B1) |S| = 2, v_k(S) > p_k; (B2) d wants Y_k and nobody else does; (B3) nobody wants Y_d;
    (B4) k values no good of Z = {Y_k, Y_d} + (J - S) other than Y_k;
    (B5) every i not in {k, d} valuing two or more goods of Z has v_i(Z) - min_Z v_i <= p_i.
    Conclusion: k: S, d: Z, everyone else its pick is EFX0 (re-checked raw here).  Returns the list of (k, d, S)."""
    import itertools
    n = P.n; J = ro['J']; W = ro['wants']; p = [P.val[i][Y[i]] for i in range(n)]
    out = []
    for d in ro['U']:
        for k in range(n):
            if k == d or (d, k) not in W or any((i, k) in W for i in range(n) if i != d): continue   # (B2)
            for S in itertools.combinations(J, 2):
                if P.u(k, S) <= p[k]: continue                                                     # (B1)
                Z = [Y[k], Y[d]] + [g for g in J if g not in S]
                if any(g in P.rel[k] for g in Z if g != Y[k]): continue                          # (B4)
                ok = True
                for i in range(n):
                    if i in (k, d): continue
                    if sum(1 for g in Z if g in P.rel[i]) >= 2 and P.threat(i, p[i], Z): ok = False; break
                if not ok: continue                                                               # (B5)
                X = [[Y[i]] for i in range(n)]; X[k] = list(S); X[d] = Z
                assert P.efx0(X), ('RF-B allocation not EFX0', Y, k, d, S)
                out.append((k, d, S))
    return out


def profile_job(task):
    sets, vals = task
    P = Prof(sets, vals); nu, mm = P.max_matchings()
    best, O = lexmax(mm, P.sigma)
    C = collections.Counter(); bad = []
    for Y in O:
        c, ro = classify(sets, vals, Y, P)
        C['sigma-optimal: ' + c] += 1
        C['  %s class (|U|,|D_T|)=(%d,%d)' % (c, len(ro['U']), len(ro['DT']))] += 1
        if c == 'F': bad.append(Y)
    C['profiles'] += 1
    return C, (sets, vals, bad) if bad else None


def rand_task(args):
    n, seed = args
    from oc1_mc2_rand import gen
    return gen(n, random.Random(seed))


if __name__ == '__main__':
    print('$ python3 k4/rkmax/rk_classes.py', *sys.argv[1:], flush=True)
    if len(sys.argv) > 1 and sys.argv[1] == 'rand':
        N, n, SEED = map(int, sys.argv[2:5])
        with mp.Pool() as pool: tasks = pool.map(rand_task, [(n, SEED * 1000003 + t) for t in range(N)])
    else:
        STRIDE = int(sys.argv[1]) if len(sys.argv) > 1 else 1
        d = json.load(gzip.open(os.path.join(ROOT, 'results', 'k4_oc1max', 'two_move_starts_n4.json.gz')))
        prof = collections.OrderedDict()
        for h in d['hypergraphs']:
            for st in h['starts']: prof[(json.dumps(h['sets']), json.dumps(st['vals']))] = (h['sets'], st['vals'])
        tasks = list(prof.values())[::STRIDE]
    print('profiles', len(tasks), flush=True)
    T = collections.Counter(); t0 = time.time()
    with mp.Pool() as pool:
        for C, bad in pool.imap_unordered(profile_job, tasks, chunksize=4):
            T.update(C)
            if bad: print('RKMAX FAILS', json.dumps({'sets': bad[0], 'vals': bad[1], 'picks': bad[2]}), flush=True)
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
