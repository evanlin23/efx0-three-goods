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
    if any(g is None and P.rel[i] for i, g in enumerate(Y)):
        # Lemma RED (k4/sdc.md §31): drop the agents reachable from pickless agents by alternating paths, with their
        # picks; pickless agents become null; classify in the reduced instance; also check OC1 at Y in I directly.
        sets2, vals2, Y2 = red_instance(P, Y)
        c2, _ = classify_fast(sets2, vals2, Y2)
        direct = P.oc1(Y)
        return 'RED:%s (OC1 in I: %s)' % (c2, direct), ro
    if any(not theta(P, Y, ro, z) for z in ro['U']): return 'T0', ro
    if sprime_cases(P, Y, ro): return "S'", ro
    base = mmlib.base_from_picks(Y); D = mmlib.dangerous(I, base)
    for k, Pch, h, H0, X, how in s_cases(I, base, D, relaxed=True, pick_too=True):
        if X is not None:
            assert P.efx0(X), ('Theorem S allocation not EFX0', sets, vals, Y)
            return 'US-not-S\'', ro          # never expected: Theorem S is a special case of Lemma S'
    if rfb_cases(P, Y, ro): return 'RFB', ro
    if P.one_absorber([frozenset([g]) for g in Y]) is not None: return 'P', ro
    r = P.oc1(Y)
    return ('GAP-M' if r == 'M' else 'F'), ro


def red_instance(P, Y):
    """Lemma RED's reduced instance I': agents T + U (U = pickless, made null), goods {Y_t : t in T} + J, relabelled
    0..m'-1; returns (sets, vals, picks)."""
    n = P.n; holder = {Y[i]: i for i in range(n) if Y[i] is not None}
    U = [i for i in range(n) if Y[i] is None]; S = set(); front = list(U); seen = set(U)
    while front:
        a = front.pop()
        for g in P.rel[a]:
            if g in holder and holder[g] not in seen:
                seen.add(holder[g]); S.add(holder[g]); front.append(holder[g])
    keep = [i for i in range(n) if i not in S]
    removed = {Y[i] for i in S}
    goods = [g for g in range(P.m) if g not in removed]; lab = {g: t for t, g in enumerate(goods)}
    sets2, vals2, Y2 = [], [], []
    for i in keep:
        if Y[i] is None: sets2.append([]); vals2.append([]); Y2.append(None); continue
        gs = sorted(g for g in P.rel[i] if g in lab)
        sets2.append([lab[g] for g in gs]); vals2.append([P.val[i][g] for g in gs]); Y2.append(lab[Y[i]])
    return sets2, vals2, tuple(Y2)


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


def sprime_cases(P, Y, ro, first=True):
    """Lemma S' (k4/rkmax.md §5; Theorem S of k4/oc1max_multi.md §10 with the kept-out good to any holder).
    k in D; P = (k = x_0, ..., x_t = z) any canonical chain (x_i wants Y_{x_{i-1}}, z unfrozen at Y); h in J + {Y_z};
    W = (J + {Y_z}) - {h}; (S'-a) v_k(W) > p_k; B' = Y after P (k: an improving H_0 inside W); r != k a holder at B'
    (one good, nobody wants it at B'); A: k gets W, r gets B'_r + {h}, everyone else B'.
    (S'-b) W threatens no agent i != k at v_i(A_i).  Then A is EFX0 and OC1 holds (one official chain, one absorber).
    Returns the list of (k, P, h, r) meeting (S'-a), (S'-b) (A re-checked raw)."""
    n = P.n; J = list(ro['J']); W_ = ro['wants']; p = [P.val[i][Y[i]] if Y[i] is not None else 0 for i in range(n)]
    out = []
    for k in ro['D']:
        chains = []
        def ext(path):
            x = path[-1]
            if len(path) >= 2 and x in ro['U']: chains.append(tuple(path))
            if x in ro['U']: return
            for y in range(n):
                if y not in path and (y, x) in W_: ext(path + [y])
        ext([k])
        for ch in chains:
            z = ch[-1]
            for h in J + [Y[z]]:
                W = [g for g in J + [Y[z]] if g != h]
                if P.u(k, W) <= p[k]: continue
                Bp = [frozenset([Y[i]]) for i in range(n)]
                Bp[k] = frozenset(g for g in W if g in P.rel[k])     # an improving H_0 inside W (k's goods of W)
                for s in range(1, len(ch)): Bp[ch[s]] = frozenset([Y[ch[s - 1]]])
                val = [P.u(i, Bp[i]) for i in range(n)]
                for r in range(n):
                    if r == k or len(Bp[r]) != 1: continue
                    g = next(iter(Bp[r]))
                    if any(i != r and P.val[i].get(g, 0) > val[i] for i in range(n)): continue   # r a holder
                    A = [set(b) for b in Bp]; A[k] = set(W); A[r] = set(Bp[r]) | {h}
                    if any(P.threat(i, P.u(i, A[i]), W) for i in range(n) if i != k): continue
                    assert P.efx0([list(a) for a in A]), ("Lemma S' allocation not EFX0", Y, k, ch, h, r)
                    out.append((k, ch, h, r))
                    if first: return out
    return out


def rfb_cases(P, Y, ro):
    """Lemma RF-B (k4/oc1_hall.md §24.8, refereed CORRECT): agents d != k, S subset of J with
    (B1) |S| = 2, v_k(S) > p_k; (B2) d wants Y_k and nobody else does; (B3) nobody wants Y_d;
    (B4) k values no good of Z = {Y_k, Y_d} + (J - S) other than Y_k;
    (B5) every i not in {k, d} valuing two or more goods of Z has v_i(Z) - min_Z v_i <= p_i.
    Conclusion: k: S, d: Z, everyone else its pick is EFX0 (re-checked raw here).  Returns the list of (k, d, S)."""
    import itertools
    n = P.n; J = ro['J']; W = ro['wants']; p = [P.val[i][Y[i]] if Y[i] is not None else 0 for i in range(n)]
    if any(Y[i] is None for i in range(n)): return []        # RF-B is stated for starts where every agent holds a good
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
