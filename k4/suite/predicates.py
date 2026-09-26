"""Candidate statements for k = 4, each evaluated on one instance by up to two independent implementations.

A predicate maps an instance record (k4/suite/instances/*.json) to a verdict:
  True   the statement holds on the instance,
  False  it fails (the instance is a counterexample),
  None   not applicable (its hypothesis is not met, e.g. omega <= 0, f != 1, not a core, or too large).
and a short detail string. `PREDICATES[name]` has the statement, its source, and `impls = {impl: fn}`; 'suite' is
k4/suite/model.py, the others are the adapters of k4/suite/ext.py. k4/suite/run.py runs them and flags disagreements.
"""
import itertools, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import model as M
import ext

BIG = 7_000_000     # skip an implementation whose enumeration would be larger than this (reported as None)


def _inst(d):
    return M.Inst(d['sets'], d['vals'], d.get('m'))


def _V(d):
    m = d.get('m') or 1 + max(g for S in d['sets'] for g in S)
    V = [[0] * m for _ in d['sets']]
    for i, (S, t) in enumerate(zip(d['sets'], d['vals'])):
        for g, x in zip(S, t): V[i][g] = x
    return V, list(range(len(d['sets']))), list(range(m))


def _gp(d):
    G = ext.gap()
    P = G.Profile(d['sets'], d['vals'], d.get('m'))
    P.preallocs()
    return P


def _ok_size(d, lim=12):
    return len(d['sets']) <= 6 and (d.get('m') or 1 + max(g for S in d['sets'] for g in S)) <= lim


# ------------------------------------------------------------------ baseline: the targets themselves
SAT_LIMIT = 60
BIG_N = 13        # model.py's SAT is slow beyond this (H_5, n = 21); #43's encoding covers those instances


def _too_big(d): return len(d['sets']) > BIG_N


BIGMSG = 'n > %d: left to the second implementation' % BIG_N


def efx0_suite(d):
    if _too_big(d): return None, BIGMSG
    X = _inst(d).efx0_search(time_limit=SAT_LIMIT); return X is not None, ''


def efx0_induct(d): V, a, g = _V(d); return ext.induct_sat().exists(V, a, g) is not None, ''


def d2_suite(d):
    if _too_big(d): return None, BIGMSG
    X = _inst(d).efx0_search(d2=True, time_limit=SAT_LIMIT); return X is not None, ''


def d2_induct(d): V, a, g = _V(d); return ext.induct_sat().exists(V, a, g, d2=True) is not None, ''


def ps_suite(d):
    if _too_big(d): return None, BIGMSG
    I = _inst(d); bad = [w for w in range(I.n) if I.efx0_search(unenvied=[w], time_limit=SAT_LIMIT) is None]
    return not bad, ('fails for agents %s' % bad) if bad else ''


def ps_induct(d):
    V, a, g = _V(d); S = ext.induct_sat()
    bad = [w for w in a if S.ps(V, a, g, w) is None]
    return not bad, ('fails for agents %s' % bad) if bad else ''


def psd2_suite(d):
    """PS-OWNER: for every agent w, an EFX0 allocation in which w is unenvied and every other bundle has <= 2 goods"""
    if _too_big(d): return None, BIGMSG
    I = _inst(d); bad = [w for w in range(I.n) if I.efx0_search(unenvied=[w], owner_big=w, time_limit=SAT_LIMIT) is None]
    return not bad, ('fails for agents %s' % bad) if bad else ''


def psd2_induct(d):
    """the same with #43's encoding: w unenvied and D2, plus a check that the big bundle (if any) is w's; if the model
    has another agent's big bundle, retry with that agent's bundle size capped by padding (reported as None)"""
    V, a, g = _V(d); S = ext.induct_sat()
    bad, unk = [], []
    for w in a:
        M_ = S.Model(V, a, g, True)
        # forbid a bundle of >= 3 goods for every agent other than w: clauses over triples
        extra = [[-M_.x[h1, j], -M_.x[h2, j], -M_.x[h3, j]] for j in a if j != w for h1, h2, h3 in itertools.combinations(g, 3)]
        X = M_.solve(extra=extra + M_.unenvied(w))
        if X is None: bad.append(w)
    return not bad, ('fails for agents %s' % bad) if bad else ''


# ------------------------------------------------------------------ C4min and its configuration form
def c4min_suite(d):
    I = _inst(d)
    if I.core_violations(): pass
    ok, Bs, o = I.c4min_deficit()
    return ok, 'f=%d omega=%d' % (I.f, I.omega)


def c4min_gap(d):
    P = _gp(d)
    if P.omega <= 0: return True, 'omega<=0'
    return P.deficit_ok(), 'f=%d omega=%d' % (P.f, P.omega)


def cfg_suite(d):
    I = _inst(d); I.preallocs()
    if I.omega <= 0: return None, 'omega<=0'
    return any(c.completable for c in I.configs()), ''


def cfg_gap(d):
    P = _gp(d)
    if P.omega <= 0: return None, 'omega<=0'
    return any(c.completable for c in P.configs()), ''


def _every_max(cs, key):
    if not cs: return None, 'no configuration'
    b = max(key(c) for c in cs); mx = [c for c in cs if key(c) == b]
    bad = [c for c in mx if not c.completable]
    return not bad, '%d maxima, %d not completable (max %s)' % (len(mx), len(bad), b)


def phip_suite(d):
    I = _inst(d); I.preallocs()
    if I.omega <= 0: return None, 'omega<=0'
    return _every_max(I.configs(), lambda c: c.phi)


def phip_gap(d):
    P = _gp(d)
    if P.omega <= 0: return None, 'omega<=0'
    return _every_max(P.configs(), lambda c: c.phi)


def phi_suite(d):
    I = _inst(d); I.preallocs()
    if I.omega <= 0: return None, 'omega<=0'
    return _every_max(I.configs(), lambda c: c.phi0)


def phi_gap(d):
    P = _gp(d)
    if P.omega <= 0: return None, 'omega<=0'
    return _every_max(P.configs(), lambda c: c.phi0)


def _rl_suite(c): return (c.r, c.Lam)


def thmZ_suite(d):
    """Theorem Z (proved): f = 0, omega >= 1 => every (r, Lam)-maximum configuration is completable"""
    I = _inst(d); I.preallocs()
    if I.f != 0 or I.omega <= 0: return None, 'f=%d omega=%d' % (I.f, I.omega)
    return _every_max(I.configs(), _rl_suite)


def thmZ_gap(d):
    P = _gp(d)
    if P.f != 0 or P.omega <= 0: return None, ''
    return _every_max(P.configs(), lambda c: (c.r, c.Lam))


def _thmF(cs, robust, r, lam):
    fr = [c for c in cs if all(robust(c, x) for x in c.frozen)]
    if not fr: return None, 'no frozen-robust configuration'
    return _every_max(fr, lambda c: (r(c), lam(c)))


def thmF_suite(d):
    """Theorem F (proved): if some min-frozen configuration is frozen-robust, every (r, Lam)-maximum among the
    frozen-robust configurations is completable"""
    I = _inst(d); I.preallocs()
    if I.omega <= 0 or I.f == 0: return None, 'f=%d omega=%d' % (I.f, I.omega)
    return _thmF(I.configs(), lambda c, x: c.robust(x), lambda c: c.r, lambda c: c.Lam)


def thmF_gap(d):
    P = _gp(d)
    if P.omega <= 0 or P.f == 0: return None, ''
    return _thmF(P.configs(), lambda c, x: c.robust(x), lambda c: c.r, lambda c: c.Lam)


# ------------------------------------------------------------------ pre-allocation potentials (k4/c4x.md, k4/hall.md)
def _pre_every(d, which, full=False):
    I = _inst(d)
    if not _ok_size(d, 13): return None, 'too large for enumeration'
    P = I.preallocs()
    if which == 'pareto': cand = I.pareto_max()
    elif which == 'pareto-minfrozen': cand = [x for x in I.pareto_max() if M.pc(x[1]) == I.f]
    elif which == 'minfrozen': cand = I.minP
    elif which == 'sumlev':
        lv = lambda Bs: sum(I.level(i, Bs[i]) for i in range(I.n))
        b = max(lv(Bs) for Bs, _ in P); cand = [x for x in P if lv(x[0]) == b]
    elif which == 'f0s':
        z = [x for x in P if x[1] == 0 or not any(M.pc(B) == 1 and B & x[1] for B in x[0])]
        z = [x for x in P if not I.frozen_of(*x)]
        if not z: return None, 'no pre-allocation without frozen agent'
        lv = lambda Bs: sum(I.level(i, Bs[i]) for i in range(I.n))
        b = max(lv(Bs) for Bs, _ in z); cand = [x for x in z if lv(x[0]) == b]
    test = (lambda Bs: I.completable_full(Bs)[0]) if full else (lambda Bs: I.removal_only(Bs)[0])
    bad = [Bs for Bs, _ in cand if not test(Bs)]
    return not bad, '%d maxima, %d not %s' % (len(cand), len(bad), 'completable' if full else 'removal-only completable')


def _pre_every_hall(d, which, full=False):
    H = ext.hall()
    if not _ok_size(d, 13): return None, 'too large for enumeration'
    vals = [dict(zip(S, V)) for S, V in zip(d['sets'], d['vals'])]
    m = d.get('m') or 1 + max(g for S in d['sets'] for g in S)
    n = len(vals)
    allP = H.all_valid(vals, m)
    v = lambda i, B: sum(vals[i].get(g, 0) for g in B)
    vec = [tuple(v(i, P[i]) for i in range(n)) for P, _ in allP]
    par = [allP[k] for k, a in enumerate(vec) if not any(all(b[i] >= a[i] for i in range(n)) and b != a for b in vec)]
    fmin = min(f for _, f in allP)
    if which == 'pareto': cand = par
    elif which == 'pareto-minfrozen': cand = [x for x in par if x[1] == fmin]
    elif which == 'minfrozen': cand = [x for x in allP if x[1] == fmin]
    else: return None, 'not implemented in hall_check'
    bad = [P for P, _ in cand if not H.completable(vals, P, m, removal_only=not full)[0]]
    return not bad, '%d maxima, %d not %s' % (len(cand), len(bad), 'completable' if full else 'removal-only completable')


def _pareto_nofrozen(d, impl):
    """every Pareto-maximal P of 𝒫 without frozen agent and with omega(P) >= 1 is removal-only completable"""
    if impl == 'suite':
        I = _inst(d); I.preallocs()
        cand = [Bs for Bs, NA in I.pareto_max() if not I.frozen_of(Bs, NA)]
        bad = [Bs for Bs in cand if not I.removal_only(Bs)[0]]
    else:
        H = ext.hall(); vals = [dict(zip(S, V)) for S, V in zip(d['sets'], d['vals'])]; m = d['m']; n = len(vals)
        allP = H.all_valid(vals, m); v = lambda i, B: sum(vals[i].get(g, 0) for g in B)
        vec = [tuple(v(i, P[i]) for i in range(n)) for P, _ in allP]
        cand = [allP[k][0] for k, a in enumerate(vec) if allP[k][1] == 0 and not any(all(b[i] >= a[i] for i in range(n)) and b != a for b in vec)]
        bad = [P for P in cand if not H.completable(vals, P, m, removal_only=True)[0]]
    return not bad, '%d Pareto-maxima without frozen agent, %d not removal-only completable' % (len(cand), len(bad))


def _bt(d, impl):
    """K4.HALL.BT (#46), without its label-collision clause: every Pareto-maximal P with the fewest frozen agents,
    omega(P) >= 1 and not removal-only completable has a frozen big-top agent (4 goods, holding its top a, a > b + c)
    or no frozen agent"""
    I = _inst(d); I.preallocs()
    def bigtop_frozen(Bs, NA):
        for x in I.frozen_of(Bs, NA):
            s = sorted(I.v[x].values(), reverse=True)
            if len(s) == 4 and s[0] > s[1] + s[2] and next(M.bits(Bs[x])) == I.top(x): return True
        return False
    if impl == 'suite':
        cand = [(Bs, NA) for Bs, NA in I.pareto_max() if M.pc(NA) == I.f]
        comp = lambda Bs: I.removal_only(Bs)[0]
    else:
        H = ext.hall(); vals = [dict(zip(S, V)) for S, V in zip(d['sets'], d['vals'])]; m = d['m']; n = len(vals)
        allP = H.all_valid(vals, m); v = lambda i, B: sum(vals[i].get(g, 0) for g in B)
        vec = [tuple(v(i, P[i]) for i in range(n)) for P, _ in allP]; fmin = min(f for _, f in allP)
        cand = []
        for k, a in enumerate(vec):
            if allP[k][1] == fmin and not any(all(b[i] >= a[i] for i in range(n)) and b != a for b in vec):
                Bs = tuple(M.mask(B) for B in allP[k][0]); NA = 0
                for i in range(n): NA |= I.needs(i, Bs[i])
                cand.append((Bs, NA))
        comp = lambda Bs: H.completable(vals, [set(M.bits(B)) for B in Bs], m, removal_only=True)[0]
    bad = [Bs for Bs, NA in cand if I.frozen_of(Bs, NA) and not bigtop_frozen(Bs, NA) and not comp(Bs)]
    return not bad, '%d Pareto-maxima at the fewest frozen agents; %d non-completable ones with frozen agents, none big-top' % (len(cand), len(bad))


def _bt_cfg(d, impl):
    """BT at the configuration level (#53's BT): every configuration that is Pareto-maximal (values of the holdings)
    among the configurations at the min-frozen keys and has no valid owner has a frozen big-top agent (4 goods,
    a > b + c, frozen on its top)"""
    if impl == 'suite':
        I = _inst(d); I.preallocs()
        if I.omega <= 0: return None, 'omega<=0'
        cs = I.configs()
        def bigtop(c, x):
            s_ = sorted(I.v[x].values(), reverse=True)
            return len(s_) == 4 and s_[0] > s_[1] + s_[2] and c.key[x] == I.top(x)
    else:
        P = _gp(d)
        if P.omega <= 0: return None, 'omega<=0'
        cs = P.configs(); bigtop = lambda c, x: c.bigtop(x)
    hv = [tuple(c.hv(i) for i in range(len(c.key))) for c in cs]
    mx = [cs[k] for k, a in enumerate(hv) if not any(all(b[i] >= a[i] for i in range(len(a))) and b != a for b in hv)]
    bad = [c for c in mx if not c.completable and not any(bigtop(c, x) for x in c.frozen)]
    return not bad, '%d Pareto-maximal configurations, %d without owner and without frozen big-top agent' % (len(mx), len(bad))


def _max_simple(d, impl):
    """#41's -U0 observation (MAX_SIMPLE of #53): some Φ′-maximum has a valid owner with C empty"""
    if impl == 'suite':
        I = _inst(d); I.preallocs()
        if I.omega <= 0: return None, 'omega<=0'
        cs = I.configs(); simple = lambda c: any(c.owner(o) == 0 for o in c.free)
    else:
        P = _gp(d)
        if P.omega <= 0: return None, 'omega<=0'
        cs = P.configs(); simple = lambda c: c.simple
    b = max(c.phi for c in cs); mx = [c for c in cs if c.phi == b]
    return any(simple(c) for c in mx), '%d maxima' % len(mx)


# ------------------------------------------------------------------ f = 1: the local improvement lemma (#51)
def lil_red(d):
    """K4.C4MIN.RED.LIL: f = 1, omega >= 1: every non-completable configuration has an M1, M4 or M5 move raising
    (r', -t, Lam) (#51's generator, k4/red_lil.py)"""
    os.environ['RFIRST'] = '1'; os.environ.pop('M2', None)
    RL, RB = ext.red_lil(), ext.red_lib()
    m = d.get('m') or 1 + max(g for S in d['sets'] for g in S)
    P = RB.Prof([dict(zip(S, V)) for S, V in zip(d['sets'], d['vals'])], m)
    f, keys = RB.fewest_frozen_le1(P)
    if f != 1 or m - 2 * P.n + 1 < 1: return None, 'f=%s' % f
    Ks = {x: RB.Key(P, g, x) for g, x in keys}
    stuck = 0; tot = 0
    for x, K in Ks.items():
        for Q, L in K.configs():
            if any(K.owner_status(Q, L, o)[2] for o in K.free): continue
            tot += 1; p0 = RL.phi(P, K, Q, L)
            if not any(RL.is_config(P, K2, Q2, L2) and RL.phi(P, K2, Q2, L2) > p0 for K2, Q2, L2 in RL.moves(P, Ks, K, Q, L)):
                stuck += 1
    return stuck == 0, '%d non-completable configurations, %d stuck' % (tot, stuck)


def lil_text(d):
    """LIL with the catalogue as #51's text states it (k4/suite/lil_text.py): f = 1, every non-completable
    configuration has an M1/M4/M5 move raising (r', -t, Lam)"""
    import lil_text as LT
    os.environ['RFIRST'] = '1'; os.environ.pop('M2', None)
    RL, RB = ext.red_lil(), ext.red_lib()
    P = RB.Prof([dict(zip(S, V)) for S, V in zip(d['sets'], d['vals'])], d['m'])
    f, keys = RB.fewest_frozen_le1(P)
    if f != 1 or d['m'] - 2 * P.n + 1 < 1: return None, 'f=%s' % f
    Ks = {x: RB.Key(P, g, x) for g, x in keys}
    stuck = tot = 0
    for x, K in Ks.items():
        for Q, L in K.configs():
            if any(K.owner_status(Q, L, o)[2] for o in K.free): continue
            tot += 1; p0 = RL.phi(P, K, Q, L)
            if not any(RL.is_config(P, K2, Q2, L2) and RL.phi(P, K2, Q2, L2) > p0 for K2, Q2, L2 in LT.text_moves(P, Ks, K, Q, L)):
                stuck += 1
    return stuck == 0, '%d non-completable configurations, %d stuck' % (tot, stuck)


def lil_gap(d):
    """the same statement with #53's move generator (pool moves, exchange-digraph cycles with any admissible pairs
    and receivers keeping part of their pair, two-agent re-partitions): a larger catalogue than M1 M4 M5, so a stuck
    configuration here is stuck for LIL too"""
    P = _gp(d)
    if P.f != 1 or P.omega < 1: return None, 'f=%d' % P.f
    phir = lambda c: (sum(1 for y in c.free if c.robust(y)), -c.t, c.Lam)
    stuck = tot = 0
    for c in P.configs():
        if c.completable: continue
        tot += 1; p0 = phir(c)
        nxt = [x[2] for x in c.pool_moves()] + [x[1] for x in c.cycle_moves(general=True, keep=True)] + [x[1] for x in c.two_agent_moves()]
        if not any(phir(x) > p0 for x in nxt): stuck += 1
    return stuck == 0, '%d non-completable configurations, %d stuck' % (tot, stuck)


# ------------------------------------------------------------------ Step 2 candidates
def count_suite(d):
    """COUNT (Route 1): some configuration at a min-frozen key is pool-optimal and has more robust free agents than
    free owners that threaten some frozen agent (with C empty). Sound: at a pool-optimal configuration every free agent
    is threatened by at most one owner (Lemma Z2 with U_y), so at least r' owners threaten no free agent (Theorem Z'),
    and one of them threatens no frozen agent either."""
    I = _inst(d); I.preallocs()
    if I.omega <= 0: return None, 'omega<=0'
    best = None
    for c in I.configs():
        if not _pool_opt(I, c): continue
        rp = sum(1 for y in c.free if c.robust(y))
        D = sum(1 for o in c.free if any(c.threatens(o, x) for x in c.frozen))
        if rp > D:
            assert any(c.owner(o) == 0 for o in c.free), 'COUNT certificate without a simple owner'
            return True, "r'=%d |D|=%d" % (rp, D)
        best = max(best or (-99,), (rp - D,))
    return False, 'best r\'-|D| = %s' % (best,)


def _pool_opt(I, c):
    for y in c.free:
        W = list(M.bits((c.Q[y] | c.L) & c.U(y)))
        if len(W) >= 1:
            b = max(I.val(y, M.mask(p)) for p in itertools.combinations(W, min(2, len(W))))
            if b > c.hv(y): return False
    return True


def count_gap(d):
    P = _gp(d)
    if P.omega <= 0: return None, 'omega<=0'
    for c in P.configs():
        if not c.pool_optimal: continue
        rp = sum(1 for y in c.free if c.robust(y))
        D = sum(1 for o in c.free if any(c.threatens(o, x) for x in c.frozen))
        if rp > D: return True, ''
    return False, ''


# ------------------------------------------------------------------ Route 4: LB4r with rule F (#44)
def _adaptive(d, opts):
    import json as _j, re, subprocess, tempfile
    A = ext.adaptive_dir()
    with tempfile.NamedTemporaryFile('w', suffix='.jsonl', delete=False) as fh:
        fh.write(_j.dumps({'sets': d['sets'], 'vals': d['vals']}) + '\n'); path = fh.name
    out = subprocess.run([sys.executable, os.path.join(A, 'adaptive_run.py'), '--profiles=' + path] + opts,
                         capture_output=True, text=True, check=True).stdout
    os.unlink(path)
    mt = re.search(r'profiles=(\d+) (.*?) fail=(\d+)', out)
    if not mt: return None, 'no result line'
    return int(mt.group(3)) == 0, mt.group(2)


def rulef(d):
    """LB4r with rule F (-A16) and at most one nested rotation (-r1) succeeds (#44's k4/adaptive.c; raw EFX0 check)"""
    if _inst(d).core_violations(): return None, 'not a k = 4 core'
    if len(d['sets']) > 13: return None, 'n > 13 (H_t for t <= 8: #44, K4.AD.*)'
    return _adaptive(d, ['-A16', '-r1'])


def lb4r_index(d):
    """LB4r with index insertion and at most three nested rotations succeeds (K4.LB4R's bounded form)"""
    if _inst(d).core_violations(): return None, 'not a k = 4 core'
    return _adaptive(d, ['-r3'])


# ------------------------------------------------------------------ potentials over 𝒫 (k4/c4x.md §2) and over configurations (k4/c4min.md §4)
PRE_POTS = ['sumlev', 'leximin', 'leximax', 'sum2l', '-frozen', '(-frozen,sumlev)', '(-frozen,leximin)', '(-frozen,slots)', 'pareto']


def _pre_feats(I, Bs, NA):
    lev = [I.level(i, Bs[i]) for i in range(I.n)]
    fr = [M.pc(Bs[i]) == 1 and bool(Bs[i] & NA) for i in range(I.n)]
    cap = [0 if fr[i] else max(0, 2 - M.pc(Bs[i])) for i in range(I.n)]
    return {'sumlev': sum(lev), 'leximin': tuple(sorted(lev)), 'leximax': tuple(sorted(lev, reverse=True)),
            'sum2l': sum(2 ** l for l in lev), '-frozen': -sum(fr), '(-frozen,sumlev)': (-sum(fr), sum(lev)),
            '(-frozen,leximin)': (-sum(fr), tuple(sorted(lev))), '(-frozen,slots)': (-sum(fr), sum(cap))}


def _pre_pot(d, pot, form, impl):
    """form 'every' / 'some': every / some maximum of pot over 𝒫 is completable (any completion, k4/c4x.md §1)"""
    if not _ok_size(d, 10): return None, 'too large for enumeration'
    if impl == 'suite':
        I = _inst(d); P = I.preallocs()
        if pot == 'pareto': mx = [Bs for Bs, _ in I.pareto_max()]
        else:
            fs = [(Bs, _pre_feats(I, Bs, NA)[pot]) for Bs, NA in P]
            b = max(f for _, f in fs); mx = [Bs for Bs, f in fs if f == b]
        comp = [I.completable_full(Bs)[0] for Bs in mx]
    else:
        C = ext.c4x_check()
        m = d.get('m') or 1 + max(g for S in d['sets'] for g in S)
        vals = [dict(zip(S, V)) for S, V in zip(d['sets'], d['vals'])]
        res = C.analyse([list(S) for S in d['sets']], m, vals)
        if pot == 'pareto':
            vec = [tuple(C.val(vals[i], B[i]) for i in range(len(vals))) for B, _, _ in res]
            mx_i = [k for k, a in enumerate(vec) if not any(all(b[i] >= a[i] for i in range(len(a))) and b != a for b in vec)]
            comp = [res[k][1] for k in mx_i]
        else:
            if pot not in res[0][2]: return None, 'not in k4/c4x_check.py'
            b = max(r[2][pot] for r in res); comp = [r[1] for r in res if r[2][pot] == b]
    ok = all(comp) if form == 'every' else any(comp)
    return ok, '%d maxima, %d completable' % (len(comp), sum(comp))


def _lev_vec(c):
    return tuple(sorted(c.I.level(i, c.H(i) & c.I.R[i]) if hasattr(c, 'I') else c.P.level(i, c.H(i) & c.P.R[i]) for i in range(len(c.key))))


CFG_POTS = {
    'r': lambda c: (c.r,), 'r,lam': lambda c: (c.r, c.Lam), 'lam': lambda c: (c.Lam,), '-t,lam': lambda c: (-c.t, c.Lam),
    '-t,leximin': lambda c: (-c.t, _lev_vec(c)), 'phi': lambda c: c.phi0, 'phi-prime': lambda c: c.phi,
}


def _cfg_pot(d, pot, impl):
    """every maximum of pot over the configurations at the min-frozen keys has a valid owner"""
    if impl == 'suite':
        I = _inst(d); I.preallocs()
        if I.omega <= 0: return None, 'omega<=0'
        cs = I.configs()
    else:
        P = _gp(d)
        if P.omega <= 0: return None, 'omega<=0'
        cs = P.configs()
    if pot == 'pareto':
        hv = [tuple(c.hv(i) for i in range(len(c.key))) for c in cs]
        mx = [cs[k] for k, a in enumerate(hv) if not any(all(b[i] >= a[i] for i in range(len(a))) and b != a for b in hv)]
        bad = [c for c in mx if not c.completable]
        return not bad, '%d Pareto-maximal configurations, %d not completable' % (len(mx), len(bad))
    return _every_max(cs, CFG_POTS[pot])


PREDICATES = {
    'efx0': dict(statement='TARGET4 on the instance: an EFX0 allocation exists', source='K4.T',
                 impls={'suite': efx0_suite, 'induct': efx0_induct}),
    'd2': dict(statement='K4.D on the instance: an EFX0 allocation with at most one bundle of more than two goods',
               source='K4.D', impls={'suite': d2_suite, 'induct': d2_induct}),
    'ps': dict(statement='PS(I, w) for every agent w: some EFX0 allocation leaves w unenvied', source='K4.IND.PS (#43)',
               impls={'suite': ps_suite, 'induct': ps_induct}),
    'psd2': dict(statement='PS-OWNER: for every agent w, an EFX0 allocation in which w is unenvied and every other bundle has <= 2 goods',
                 source='this PR (Route 2)', impls={'suite': psd2_suite, 'induct': psd2_induct}),
    'c4min': dict(statement='C4min (deficit form): some min-frozen P in 𝒫 is removal-only completable', source='K4.C4X.MIN',
                  impls={'suite': c4min_suite, 'gap': c4min_gap}),
    'c4min-cfg': dict(statement='C4min (configuration form): omega >= 1 => some configuration at a min-frozen key has a valid owner',
                      source='k4/c4min.md §1 (#41)', impls={'suite': cfg_suite, 'gap': cfg_gap}),
    'phi-prime': dict(statement="Conjecture Φ′: every Φ′ = (−t, r, Λ, −p)-maximum configuration has a valid owner", source='K4.C4MIN.PHI (#41)',
                      impls={'suite': phip_suite, 'gap': phip_gap}),
    'phi': dict(statement='Conjecture Φ: every Φ = (−t, r, Λ)-maximum configuration has a valid owner', source='k4/c4min.md §4 (#41)',
                impls={'suite': phi_suite, 'gap': phi_gap}),
    'thmZ': dict(statement='Theorem Z (proved): f = 0 => every (r, Λ)-maximum configuration has a valid owner', source='K4.C4MIN.Z.LEAN',
                 impls={'suite': thmZ_suite, 'gap': thmZ_gap}),
    'thmF': dict(statement='Theorem F (proved): some frozen-robust configuration => every (r, Λ)-maximum among them has a valid owner',
                 source='k4/c4min.md §3.6 (#41, Lean #55)', impls={'suite': thmF_suite, 'gap': thmF_gap}),
    'pareto': dict(statement='every Pareto-maximal P in 𝒫 is removal-only completable (Theorem K3 at k = 4)', source='K4.C4X.PHI',
                   impls={'suite': lambda d: _pre_every(d, 'pareto'), 'hall': lambda d: _pre_every_hall(d, 'pareto')}),
    'pareto-full': dict(statement='every Pareto-maximal P in 𝒫 is completable (any completion, k4/c4x.md §1)', source='K4.C4X.PHI',
                        impls={'suite': lambda d: _pre_every(d, 'pareto', True), 'hall': lambda d: _pre_every_hall(d, 'pareto', True)}),
    'pareto-minfrozen': dict(statement='every Pareto-maximal P with the fewest frozen agents is removal-only completable', source='K4.HALL.* (#46)',
                             impls={'suite': lambda d: _pre_every(d, 'pareto-minfrozen'), 'hall': lambda d: _pre_every_hall(d, 'pareto-minfrozen')}),
    'minfrozen': dict(statement='every P with the fewest frozen agents is removal-only completable', source='K4.C4X.PHI (−frozen, every)',
                      impls={'suite': lambda d: _pre_every(d, 'minfrozen'), 'hall': lambda d: _pre_every_hall(d, 'minfrozen')}),
    'sumlev': dict(statement='every Σℓ-maximum of 𝒫 is removal-only completable', source='K4.C4X.PHI',
                   impls={'suite': lambda d: _pre_every(d, 'sumlev')}),
    'f0s': dict(statement='K4.HALL.F0S: among the P without frozen agent (if any), every Σℓ-maximum is removal-only completable',
                source='K4.HALL.F0S (#46)', impls={'suite': lambda d: _pre_every(d, 'f0s')}),
    'pareto-T:bt': dict(statement='every Pareto-maximum of 𝒫_bt (big-top agents may hold their lower triple) is removal-only completable',
                        source='this PR (k4/suite/triples.py)', impls={'suite': lambda d: __import__('triples').pareto_every(d, 'bt')}),
    'pareto-T:low': dict(statement='every Pareto-maximum of 𝒫_low (every 4-good agent may hold its lower triple) is removal-only completable',
                         source='this PR (k4/suite/triples.py)', impls={'suite': lambda d: __import__('triples').pareto_every(d, 'low')}),
    'lil-text': dict(statement="LIL with the catalogue as #51's text states it (M1; M4 plain or one Lemma R (iii) receiver; M5 with x's best pair), potential (r′, −t, Λ)",
                     source='#51 (reviews)', impls={'suite+red_lib': lil_text}),
    'pareto-nofrozen': dict(statement='every Pareto-maximal P in 𝒫 without frozen agent (omega >= 1) is removal-only completable',
                            source='attempts/k4-hall-pareto-no-frozen.md (#46)',
                            impls={'suite': lambda d: _pareto_nofrozen(d, 'suite'), 'hall': lambda d: _pareto_nofrozen(d, 'hall')}),
    'bt': dict(statement='K4.HALL.BT (without the label-collision clause): a non-completable Pareto-maximum at the fewest frozen agents has a frozen big-top agent or no frozen agent',
               source='K4.HALL.BT (#46, refuted in #52)', impls={'suite': lambda d: _bt(d, 'suite'), 'hall': lambda d: _bt(d, 'hall')}),
    'bt-cfg': dict(statement='BT at the configuration level: a Pareto-maximal configuration without a valid owner has a frozen big-top agent',
                   source='BT of k4/gap_bench.py (#53), K4.HALL.BT', impls={'suite': lambda d: _bt_cfg(d, 'suite'), 'gap': lambda d: _bt_cfg(d, 'gap')}),
    'max-simple': dict(statement='some Φ′-maximum has a valid owner with C empty (#41 -U0)', source='k4/c4min.md §4 (#41), MAX_SIMPLE (#53)',
                       impls={'suite': lambda d: _max_simple(d, 'suite'), 'gap': lambda d: _max_simple(d, 'gap')}),
    'lil': dict(statement="K4.C4MIN.RED.LIL (f = 1): every non-completable configuration has an M1/M4/M5 move raising (r′, −t, Λ)",
                source='#51', impls={'red': lil_red, 'gap': lil_gap}),
    'rulef': dict(statement='LB₄ʳ with rule F (first agent by lookahead, then index order) and at most one rotation succeeds',
                  source='K4.AD.* (#44)', impls={'adaptive': rulef}),
    'lb4r-index': dict(statement='LB₄ʳ with index insertion and at most three rotations succeeds', source='K4.LB4R, K4.C4.C',
                       impls={'adaptive': lb4r_index}),
    **{'pre-%s:%s' % (form, pot): dict(statement='%s maximum of %s over 𝒫 is completable' % (form, pot), source='k4/c4x.md §2 (#36)',
                                        impls={'suite': (lambda d, p=pot, f=form: _pre_pot(d, p, f, 'suite')),
                                               'c4x': (lambda d, p=pot, f=form: _pre_pot(d, p, f, 'c4x'))})
       for pot in PRE_POTS for form in ('every', 'some')},
    **{'cfg:%s' % pot: dict(statement='every maximum of %s over the configurations at the min-frozen keys has a valid owner' % pot,
                            source='k4/c4min.md §4 (#41), attempts/k4-c4min-potentials.md',
                            impls={'suite': (lambda d, p=pot: _cfg_pot(d, p, 'suite')), 'gap': (lambda d, p=pot: _cfg_pot(d, p, 'gap'))})
       for pot in list(CFG_POTS) + ['pareto']},
    'count': dict(statement="COUNT: some pool-optimal configuration at a min-frozen key has r′ > |D| (D = free owners threatening a frozen agent)",
                  source='this PR (Route 1)', impls={'suite': count_suite, 'gap': count_gap}),
}
