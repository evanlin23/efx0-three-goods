#!/usr/bin/env python3
"""The (T3) moves out of Theorem Z′'s configurations at f = 1 (workstream proof/k4-sx; k4/sx.md). EVIDENCE tooling.

Setting: a strict profile with fewest frozen agents f = 1 and omega >= 1; a key κ = (g, x) whose least deficit def*(κ)
is positive (no configuration at κ is completable, k4/c4min.md Lemma 1). Q ranges over the configurations at κ that
maximize (r', Λ') (Theorem Z′ of k4/c4min_reduce.md §2: r' = robust free agents, Λ' = sum of the levels of the free
agents' holdings over R_y). P_Q is the state of Q (bases {g} for x, Q_y ∩ U_y for y free; k4/c4min.md Lemma 1(a)).
For each Q the tool records:
  V   the free-valid owners (Q_o ∪ L threatens no free agent holding its pair); T the terminals (needers of g);
  t   whether the pool alone threatens x; the type of x (3, BT big-top, bc, bcbd, flat as in k4/c4min_reduce.md §3);
  the regime: I if V ∩ T is nonempty, II otherwise;
  every (T3) move from P_Q (role swap with a needer z, at most one helper h giving up a good) with def(P') < def*(κ)
  ("direct" moves), classified by the role of z (zV: in V; zT: a terminal outside V), the helper (none, in V, other),
  and who is a best owner of P';
  the canonical moves of k4/sx.md:
    OS  (owner swap) for o in V ∩ T: o takes {g}, x takes an admissible A ⊆ Q_o ∪ L, x owns Q_o ∪ L;
        "theta-b" when o is big-top on g with U_o ⊆ Q_o ∪ L and omega >= 2;
    OSd (owner swap, d dropped) for a theta-b o: x owns (Q_o ∪ L) minus o's fourth good;
    L7  (Lemma 7 swap, regime II) z the unique terminal takes {g}, the helper o in V gives up the goods of R_x it holds
        (keeps the rest of its pair as base when admissible, or its best admissible set otherwise), x takes its two best
        lower goods and owns R_x minus g plus the pool plus what o released, minus o's kept base.
Each canonical move is evaluated exactly (the deficit of P' by Lemma H1) and, for OS/OSd, also by the explicit bundle.

usage: python3 k4/sx_zprime.py DUMP.jsonl.gz ... [--examples=K]      (dumps of k4/sx_keygraph.py --dump)
       python3 k4/sx_zprime.py catalog FILE [--every=E] [--max=N] [--examples=K]"""
import collections, gzip, itertools, json, os, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, 'suite'))
import model as M
from model import bits, pc, mask
from dl2_classify import PA, INF
from sx_keygraph import KeyProfile, keyof


def xtype(I, x):
    vs = sorted(I.v[x].values(), reverse=True)
    if len(vs) == 3: return '3'
    a, b, c, d = vs
    if a > b + c: return 'BT'
    if a > b + d: return 'bc'
    if a > c + d: return 'bcbd'
    return 'flat'


def bigtop_on(I, y, g):
    if len(I.sets[y]) != 4: return False
    vs = sorted(I.v[y].values(), reverse=True)
    return I.v[y].get(g) == vs[0] and vs[0] > vs[1] + vs[2]


def owner_value(P, o, Z):
    """|Z| + u_o(Z) if Z is a safe bundle of the free o in P, else None"""
    if Z & ~(P.Bs[o] | P.J) or P.Bs[o] & ~Z: return None
    if not P.safe(o, Z): return None
    return pc(Z) + P.u(o, Z)


def kind(I, c, y, U):
    """the kind of a free agent y of the pool-optimal configuration c (k4/c4min_f1.md Lemma 3): 'rob' (robust),
    'T3', 'T4', 'Tg', 'D', 'R', or '?' (none: would contradict Lemma 3)"""
    if c.robust(y): return 'rob'
    H = c.Q[y] & U[y]
    gs = sorted(bits(U[y]), key=lambda h: -I.v[y][h])
    if pc(U[y]) == 2: return '?'
    if pc(U[y]) == 3:
        if pc(I.R[y]) == 3: return 'T3' if H == 1 << gs[0] else '?'
        return 'Tg' if H == 1 << gs[0] else '?'
    a, b, cc, d = gs
    if H == 1 << a: return 'T4'
    if H == (1 << a) | (1 << d): return 'D'
    if not H & (1 << a) and pc(H) == 2: return 'R'
    return '?'


def gpm_check(kp, k, c, V, T, X, nb_T3, cnt, ex, nex, tag):
    """the threat forest (k4/sx.md Lemma F) and the generalized path move (Proposition B): for every terminal tau
    outside V and every threat path tau -> q1 -> ... -> qk = o (o in V), the configuration at (g, tau) in which
    q_i takes Q_{q_{i-1}}, x takes a pair inside X_o = Q_o ∪ L with admissible part, tau takes g and x owns X_o, is
    a configuration with x a valid owner (C = ∅), unless o is of kind (R) with its fourth good in L"""
    I = kp.I
    x = next(i for i in range(I.n) if k[i] is not None); g = k[x]; gm = 1 << g
    free = [i for i in range(I.n) if i != x]
    U = {y: I.R[y] & ~gm for y in range(I.n)}
    out = {o: [y for y in free if y != o and I.threat(y, X[o], c.hv(y))] for o in free}
    indeg = collections.Counter(y for o in free for y in out[o])
    assert all(indeg[y] <= 1 for y in free), 'Lemma F: a free agent with two threateners'
    assert all(indeg[y] == 0 for y in free if c.robust(y)), 'Lemma F: a robust agent threatened'
    assert set(V) == {o for o in free if not out[o]}, 'Lemma F: V is not the set of leaves'
    seen = {}
    def dfs(u, st):            # acyclicity
        seen[u] = 1
        for w in out[u]:
            assert seen.get(w) != 1, 'Lemma F: a threat cycle among free agents'
            if w not in seen: dfs(w, st)
        seen[u] = 2
    for o in free:
        if o not in seen: dfs(o, None)
    kinds = {y: kind(I, c, y, U) for y in free}
    assert all(kinds[y] != '?' for y in free), ('F1 Lemma 3 kinds', kinds)
    case = set()
    for tau in T:
        if tau in V: continue
        paths = []
        def walk(u, path):
            if not out[u]: paths.append(path); return
            for w in out[u]: walk(w, path + [w])
        walk(tau, [tau])
        for path in paths:
            o = path[-1]; kk = len(path) - 1
            sL = False
            if kinds[o] == 'R':
                ao = max(bits(U[o]), key=lambda h: I.v[o][h])
                s4 = next(bits(U[o] & ~(c.Q[o] | (1 << ao))))   # o's fourth good s_o (R_o = {a, p, q, s})
                sL = bool(c.L >> s4 & 1)
            cnt['%s GPM paths k=%d leaf kind=%s%s' % (tag, kk, kinds[o], ' s in L' if sL else '')] += 1
            if sL:
                case.add('Rs')
                # the modified move (Proposition B'): o takes {a_o, s_o}, the other good y of Q_{q_{k-1}} joins x's bundle
                Q2 = dict(c.Q)
                for i in range(1, len(path) - 1): Q2[path[i]] = c.Q[path[i - 1]]
                prev = c.Q[path[-2]]
                assert prev >> ao & 1
                Q2[o] = (1 << ao) | (1 << s4)
                y = prev & ~(1 << ao)
                X2 = (X[o] & ~(1 << s4)) | y
                del Q2[tau]
                key2 = tuple(g if i == tau else None for i in range(I.n))
                okB2 = False
                hB = not any(I.R[w] & y for w in range(I.n) if w != x)
                cnt["%s Prop B' k=%d hypothesis (y valued only by x) holds=%s" % (tag, kk, hB)] += 1
                for pr in itertools.combinations(list(bits(X2)), 2):
                    P2 = mask(pr)
                    if not (P2 & U[x] and I.admissible(x, P2 & U[x], U[x])): continue
                    Q3 = dict(Q2); Q3[x] = P2
                    c2 = M.Config(I, key2, Q3)
                    assert all(I.admissible(w, c2.Q[w] & U[w], U[w]) for w in c2.free)
                    if c2.owner(x) == 0: okB2 = True; break
                    assert not hB, ("Proposition B' failed under its hypothesis", kp.d, k, repr(c), path, sorted(bits(P2)))
                cnt["%s Prop B' (modified path move) k=%d works=%s" % (tag, kk, okB2)] += 1
                if okB2 and hB:
                    case.add("B1'" if kk == 1 else "Bk'")
                continue
            # build the configuration at (g, tau)
            Q2 = dict(c.Q)
            for i in range(1, len(path)): Q2[path[i]] = c.Q[path[i - 1]]
            del Q2[tau]
            Xo = X[o]
            pair = None
            for pr in itertools.combinations(list(bits(Xo)), 2):
                P2 = mask(pr)
                if P2 & U[x] and I.admissible(x, P2 & U[x], U[x]): pair = P2; break
            assert pair is not None, 'Proposition B: x has no admissible pair inside X_o'
            Q2[x] = pair
            key2 = tuple(g if i == tau else None for i in range(I.n))
            assert key2 in kp.K, ('Proposition B: (g, tau) is not a key', key2)
            for y, P2 in Q2.items():
                assert I.admissible(y, P2 & U[y], U[y]), ('Proposition B: a pair without admissible part', y)
            L2 = Xo & ~pair
            used = 0
            for P2 in Q2.values():
                assert not P2 & used; used |= P2
            assert not used & L2 and not (used | L2) & gm and pc(used | L2) == I.m - 1
            H2 = {y: Q2[y] for y in Q2}; H2[tau] = gm
            bad = [y for y in H2 if y != x and I.threat(y, Xo, I.val(y, H2[y]))]
            assert not bad, ('Proposition B: x is not a valid owner', kp.d, k, repr(c), path, bad)
            assert kp.dstar[key2] <= 0, 'Proposition B: the key (g, tau) has positive def*'
            adj = key2 in nb_T3
            cnt['%s GPM ok k=%d adjacent(T3)=%s' % (tag, kk, adj)] += 1
            case.add('B1' if kk == 1 else ('Bk-adj' if adj else 'Bk-nonadj'))
    return case


def analyse_key(kp, k, cnt, ex, nex, nb):
    I = kp.I
    x = next(i for i in range(I.n) if k[i] is not None); g = k[x]; gm = 1 << g
    free = [i for i in range(I.n) if i != x]
    U = {y: I.R[y] & ~gm for y in range(I.n)}
    cs = I.configs([k])
    lev = lambda c: sum(I.level(y, c.Q[y] & I.R[y]) for y in free)
    rob = lambda c: sum(1 for y in free if c.robust(y))
    best = max((rob(c), lev(c)) for c in cs)
    mx = [c for c in cs if (rob(c), lev(c)) == best]
    ds = kp.dstar[k]; xt = xtype(I, x); om = I.omega
    cnt['keys'] += 1; cnt['keys xtype=%s' % xt] += 1
    for c in mx:
        cnt['Zmax'] += 1
        Bs = tuple(gm if i == x else (c.Q[i] & U[i]) for i in range(I.n))
        P = kp.PA[Bs]
        X = {o: c.Q[o] | c.L for o in free}
        V = [o for o in free if not any(I.threat(y, X[o], c.hv(y)) for y in free if y != o)]
        T = [z for z in free if P.N[z] & gm]
        thx = [o for o in free if I.threat(x, X[o], I.v[x][g])]
        t = int(I.val(x, c.L & U[x]) > I.v[x][g])
        VT = [o for o in V if o in T]
        regime = 'I' if VT else 'II'
        assert V, 'Theorem Z′ violated: no free-valid owner'
        assert all(o in thx for o in V), 'a free-valid owner that spares x: the key would be completable'
        assert pc(c.L) == om
        tag = 'regime %s' % regime
        cnt[tag] += 1
        cnt['%s |V|=%d |T|=%d |VT|=%d t=%d x=%s' % (tag, len(V), len(T), len(VT), t, xt)] += 1
        # direct T3 moves
        mv = [m for m in kp.t3plus_moves(Bs) if not m[3]]
        direct = [m for m in mv if kp.D[m[0]] < ds]
        cnt['%s Zmax with a direct T3 move' % tag] += bool(direct)
        kinds = set()
        for b2, xx, z, W, h in direct:
            P2 = kp.PA[b2]
            dv, res2 = P2.deficit()
            mv2 = max(b for b, _ in res2.values())
            own = sorted(o for o, (b, _) in res2.items() if b == mv2)
            kinds.add(('zV' if z in V else 'zT', '-' if h is None else ('hV' if h in V else 'h'),
                       'own=x' if x in own else ('own=V' if any(o in V for o in own) else 'own=other')))
        for kd in kinds: cnt['%s direct kind %s' % (tag, kd)] += 1
        if not direct:
            cnt['NO DIRECT MOVE'] += 1
            if len(ex['nodirect']) < nex: ex['nodirect'].append((kp.d, k, repr(c)))
        # canonical OS
        os_ok = False; os_ok_nothb = False
        for o in VT:
            thb = bigtop_on(I, o, g) and not (U[o] & ~X[o]) and om >= 2
            cnt['%s OS o theta-b=%s' % (tag, thb)] += 1
            for kk in (1, 2):
                for Acomb in itertools.combinations(list(bits(X[o] & U[x])), kk):
                    A = mask(Acomb)
                    if not I.admissible(x, A, U[x]): continue
                    b2 = list(Bs); b2[o] = gm; b2[x] = A; b2 = tuple(b2)
                    assert b2 in kp.S, 'Lemma 6 violated'
                    P2 = kp.PA[b2]
                    val = owner_value(P2, x, X[o])
                    if not thb:
                        assert val is not None and val >= om + 2, ('owner swap failed without theta-b', kp.d, k, repr(c), o)
                        assert kp.D[b2] <= 0
                        os_ok = True; os_ok_nothb = True
                    else:
                        assert val is None
                        dsub = X[o] & ~(U[o] & ~c.Q[o])     # drop o's fourth good
                        v2 = owner_value(P2, x, dsub)
                        okd = kp.D[b2] < ds
                        cnt['%s OS theta-b: exact def(P\')<def* %s, OSd bundle value %s (omega+2=%d), T=%s' % (
                            tag, okd, v2, om + 2, 'single' if len(T) == 1 else 'several')] += 1
                        if okd: os_ok = True
                    break
                else:
                    continue
                break
        cnt['%s OS succeeds' % tag] += os_ok
        # Proposition C (a theta-b terminal leaf tau1 hands g over, x takes a robust pair P_x inside X_tau1 meeting U_tau1,
        # another leaf o owns Q_o ∪ (X_tau1 minus P_x)); hypothesis (H): that bundle threatens no free agent outside {o, tau1}
        caseC = False; caseCH = False
        for t1 in VT:
            if not (bigtop_on(I, t1, g) and not (U[t1] & ~X[t1]) and om >= 2): continue
            key2 = tuple(g if i == t1 else None for i in range(I.n))
            for o in V:
                if o == t1: continue
                for pr in itertools.combinations(list(bits(X[t1])), 2):
                    Px = mask(pr)
                    if not (Px & U[x] and I.admissible(x, Px & U[x], U[x])): continue
                    if I.val(x, Px) < I.val(x, U[x] & ~Px) or not Px & U[t1]: continue
                    Y = c.Q[o] | (X[t1] & ~Px)
                    hstar = not any(I.R[y] & c.Q[t1] & ~Px for y in free if y not in (o, t1))
                    if hstar:
                        assert not any(I.threat(y, Y, c.hv(y)) for y in free if y not in (o, t1)), "(H*) does not give (H)"
                    else:
                        caseCH = True; continue
                    Q2 = dict(c.Q); del Q2[t1]; Q2[x] = Px
                    c2 = M.Config(I, key2, Q2)
                    assert key2 in kp.K and c2.owner(o) == 0, ('Proposition C failed', kp.d, k, repr(c), t1, o, Px)
                    b2 = list(Bs); b2[t1] = gm; b2[x] = Px & U[x]; b2 = tuple(b2)
                    assert b2 in kp.S and kp.D[b2] <= 0, 'Proposition C: the T3 image'
                    caseC = True
        cnt['%s Prop C applies=%s (only (H) missing=%s)' % (tag, caseC, caseCH and not caseC)] += 1
        # Proposition C' (two terminals, both leaves, tau1 theta-b): T = {tau1, tau2}; x takes a robust pair P inside
        # X_tau1 worth more than g to x; tau2 owns Y = (X_tau2 ∪ Q_tau1) minus P and one good w of U_tau1 outside P,
        # with U_tau2 ⊆ Y (tau2 stops needing g, tau1 is unfrozen); (H'): Y threatens no free agent outside {tau1, tau2}
        caseC2 = False; caseC2H = False
        if len(T) == 2 and set(T) <= set(V):
            for t1 in T:
                t2 = next(z for z in T if z != t1)
                if not (bigtop_on(I, t1, g) and not (U[t1] & ~X[t1]) and om >= 2): continue
                for pr in itertools.combinations(list(bits(X[t1])), 2):
                    Px = mask(pr)
                    if not (Px & U[x] and I.admissible(x, Px & U[x], U[x])): continue
                    if I.val(x, Px) < I.val(x, U[x] & ~Px) or I.val(x, Px) <= I.v[x][g]: continue
                    for w in bits(U[t1] & ~Px):
                        Y = (X[t2] | c.Q[t1]) & ~Px & ~(1 << w)
                        if U[t2] & ~Y: continue
                        hstar = not any(I.R[y] & c.Q[t1] & ~Px & ~(1 << w) for y in free if y not in (t1, t2))
                        if hstar:
                            assert not any(I.threat(y, Y, c.hv(y)) for y in free if y not in (t1, t2)), "(H'*) does not give (H')"
                        else:
                            caseC2H = True; continue
                        b2 = list(Bs); b2[t1] = gm; b2[x] = Px & U[x]; b2 = tuple(b2)
                        assert b2 in kp.S, "Proposition C': the T3 image is not a state"
                        val = owner_value(kp.PA[b2], t2, Y)
                        assert val is not None and val >= om + 2 and kp.D[b2] <= 0, ("Proposition C' failed", kp.d, k, repr(c), t1, Px, w)
                        caseC2 = True
        cnt["%s Prop C' applies=%s (only (H') missing=%s)" % (tag, caseC2, caseC2H and not caseC2)] += 1
        case = gpm_check(kp, k, c, V, T, X, nb['T3'][k], cnt, ex, nex, tag)
        if os_ok_nothb: case.add('A')
        if os_ok: case.add('A*')
        if caseC: case.add('C')
        if caseC2: case.add("C'")
        if caseCH: case.add('C-H')
        cnt['%s cases %s' % (tag, ','.join(sorted(case)) or 'none')] += 1
        main_case = next((cc for cc in ('A', 'B1', 'C', "C'", "B1'", 'Bk-adj', 'Bk-nonadj', "Bk'") if cc in case), 'rest')
        cnt['MAIN CASE %s' % main_case] += 1
        if main_case == 'rest' and len(ex['rest']) < nex: ex['rest'].append((kp.d, k, repr(c), 'V', V, 'T', T, sorted(case)))
        if regime == 'I' and not os_ok and len(ex['I-no-OS']) < nex:
            ex['I-no-OS'].append((kp.d, k, repr(c), 'V', V, 'T', T, sorted(kinds)))
        if regime == 'II' and len(ex['II']) < nex:
            ex['II'].append((kp.d, k, repr(c), 'V', V, 'T', T, 'thx', thx, 't', t, xt, sorted(kinds)))


def main(argv):
    if not argv: print(__doc__); return
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    rest = [a for a in argv if not a.startswith('--')]
    nex = int(opt.get('examples', 3))
    print('# command: python3 k4/sx_zprime.py ' + ' '.join(argv), flush=True)
    profs = []
    if rest[0] == 'catalog':
        recs = json.load(gzip.open(rest[1], 'rt'))['records']
        recs = [r for r in recs if r.get('f', 1) == 1][::int(opt.get('every', 1))]
        if 'max' in opt: recs = recs[:int(opt['max'])]
        profs = [{'sets': r['core']['sets'], 'vals': r['vals'], 'm': r['core']['m']} for r in recs]
    else:
        for fn in rest:
            for line in gzip.open(fn, 'rt'):
                r = json.loads(line)
                if r['f'] == 1: profs.append({'sets': r['sets'], 'vals': r['vals'], 'm': r['m']})
    cnt = collections.Counter(); ex = collections.defaultdict(list); t0 = time.time()
    for d in profs:
        kp = KeyProfile(d)
        if not kp.ok or kp.I.f != 1: continue
        nb = kp.neighbours()
        for k in kp.K:
            if kp.dstar[k] > 0: analyse_key(kp, k, cnt, ex, nex, nb)
    for k in sorted(cnt): print('%-100s %d' % (k, cnt[k]))
    for k, v in ex.items():
        for e in v: print('EX', k, e)
    print('# time %.1f s' % (time.time() - t0))


if __name__ == '__main__':
    main(sys.argv[1:])
