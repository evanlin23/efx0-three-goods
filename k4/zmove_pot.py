#!/usr/bin/env python3
"""Theorem ZMOVE by a potential argument (workstream proof/k4-zmove-pot, k4/zmove_pot.md). EVIDENCE tooling.

For every strict profile with f >= 1, omega >= 1 and every key k with def*(k) > 0 (k4/sx.md §1), on the states of k
(the min-frozen P with key k):
  zm(P)   some (T3+) move from P with at most one helper (giving up a good of its base) reaches a min-frozen P' with
          def(P') <= 0 (ledger K4.DL2.RC's (T3+); k4/sx_keygraph.KeyProfile.t3plus_moves);
  classes of states, each a candidate potential in the "every" form ("zm(P) at every state of the class"):
          ALL      every state
          U        every free agent locally optimal: no set S of at most two goods inside (B_y ∪ J) ∩ R_y with
                   v_y(S) > v_y(B_y)
          PARETO   no state of the key at least as good for every free agent and better for one
          R        the number r' of robust free agents (v_y(B_y) >= v_y(U_y \\ B_y), U_y = R_y minus the needed set)
                   is maximal
          RU       R and U
          RPARETO  R, and Pareto among the r'-maximal states
          LAM      Λ' = Σ_y ℓ_y(B_y) maximal (levels over the subsets of R_y, k4/sx.md §2)
          RLAM     (r', Λ') maximal: the states P_Q of the Z'-maxima Q (k4/zmove_pot.md §3, Lemma Z0)
  plus the configuration-level potential (-t, r', Λ') of k4/c4min.md §4 (t: frozen agents threatened by the pool
  alone), over every configuration of the key (model.Inst.configs): label TRL (every maximum's P_Q).
  With --indep=E, every E-th profile is recomputed by main's repo-free k4/rt4_n5_indep.py (its own 𝒫, deficits and
  (T3+) test): every state's deficit, every def*, and zm at every state are asserted equal.
Theorem AR (k4/zmove_pot.md §4) at every state of every f = 1 key with def* > 0 at which every free agent is robust and
every terminal (free needer of g) is locally optimal: the case (1, 2, 3C, 3C', 3x, 3p, or the residual), and for
cases 1-3p the move the proof constructs, with def(P') <= 0 asserted from the exact deficits.

Also counted per key with def* > 0: the number of free agents that are not robust at its Z'-maxima (the same at every
Z'-maximum, since they all have the maximal r'; k4/zmove_pot.md §5). At f >= 2, at every state of such a key at which
every free agent is robust and locally optimal (the hypotheses of Theorem AR): whether zm holds, whether it holds with
a move without helper, and with a plain (T3) move without helper (k4/zmove_pot.md §6).

usage: python3 k4/zmove_pot.py [--every=E] [--indep=E] [--max=N] [--tmax=S] [--fmax=F] INPUT ...
INPUT: a gzip JSON-lines dump with sets/vals/m (k4/sx_hunt.py, k4/sx_keygraph.py --dump, compute/k4-cover's hunts) or
inst:FILE.json (a JSON list of {sets, vals, m}). Profiles are deduplicated across inputs."""
import collections, gzip, itertools, json, os, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, 'suite'))
import model as M
from model import bits, pc, mask
from sx_keygraph import KeyProfile, keyof

CLASSES = ('ALL', 'U', 'PARETO', 'R', 'RU', 'RPARETO', 'LAM', 'RLAM', 'TRL')


def lst(Bs): return [sorted(bits(B)) for B in Bs]


# ------------------------------------------------------------------------------------------------ implementation A
def zm_moves(kp, Bs):
    """the (T3+) moves (<= 1 helper) from Bs to a state of deficit <= 0: [(b2, x, z, W, h)]"""
    return [mv for mv in kp.t3plus_moves(Bs) if kp.D[mv[0]] <= 0]


def key_classes(kp, k):
    """{class: [states]} for the key k (states as base tuples)"""
    I = kp.I
    free = [y for y in range(I.n) if k[y] is None]
    Nm = mask(g for g in k if g is not None)
    U = {y: I.R[y] & ~Nm for y in range(I.n)}
    sts = kp.K[k]
    vec = {b: tuple(I.val(y, b[y]) for y in free) for b in sts}
    rob = {b: sum(1 for y in free if I.val(y, b[y]) >= I.val(y, U[y] & ~b[y])) for b in sts}
    lam = {b: sum(I.level(y, b[y]) for y in free) for b in sts}

    def uopt(b):
        J = kp.PA[b].J
        for y in free:
            pool = list(bits((b[y] | J) & I.R[y]))
            for r in (1, 2):
                for c in itertools.combinations(pool, r):
                    if I.val(y, mask(c)) > I.val(y, b[y]): return False
        return True

    def dominated(b, among):
        return any(all(a >= c for a, c in zip(vec[b2], vec[b])) and vec[b2] != vec[b] for b2 in among)

    mr = max(rob.values()); ml = max(lam.values()); mrl = max((rob[b], lam[b]) for b in sts)
    U_ = [b for b in sts if uopt(b)]
    Rm = [b for b in sts if rob[b] == mr]
    out = {'ALL': list(sts), 'U': U_, 'PARETO': [b for b in sts if not dominated(b, sts)], 'R': Rm,
           'RU': [b for b in Rm if b in set(U_)], 'RPARETO': [b for b in Rm if not dominated(b, Rm)],
           'LAM': [b for b in sts if lam[b] == ml], 'RLAM': [b for b in sts if (rob[b], lam[b]) == mrl]}
    # configuration level: (-t, r', Λ') over all configurations of the key
    cs = I.configs([k])
    if cs:
        def phi(c): return (-c.t, sum(1 for y in free if c.robust(y)), sum(I.level(y, c.Q[y] & I.R[y]) for y in free))
        best = max(phi(c) for c in cs)
        out['TRL'] = sorted(set(tuple((1 << k[i]) if k[i] is not None else (c.Q[i] & U[i]) for i in range(I.n))
                                for c in cs if phi(c) == best))
    else:
        out['TRL'] = []
    return out, rob, U


# ------------------------------------------------------------------------------------------------ Theorem AR (f = 1)
def bigtop_on(I, y, g):
    if len(I.sets[y]) != 4: return False
    vs = sorted(I.v[y].values(), reverse=True)
    return I.v[y].get(g) == vs[0] and vs[0] > vs[1] + vs[2]


def locally_optimal(I, P, y):
    pool = list(bits((P.Bs[y] | P.J) & I.R[y]))
    return not any(I.val(y, mask(c)) > I.val(y, P.Bs[y]) for r in (1, 2) for c in itertools.combinations(pool, r))


def theorem_ar(kp, k, Bs, cnt, ex, d):
    """k4/zmove_pot.md §4 at the f = 1 state Bs (every free agent robust, every terminal locally optimal): returns the
    case; asserts that the move of the case reaches a state of deficit <= 0"""
    I = kp.I; P = kp.PA[Bs]; om = I.omega
    x = next(i for i in range(I.n) if k[i] is not None); g = k[x]; gm = 1 << g
    free = [y for y in range(I.n) if y != x]
    U = {y: I.R[y] & ~gm for y in range(I.n)}
    J = P.J; S = sum(2 - pc(Bs[y]) for y in free)
    T = [z for z in free if P.N[z] & gm]
    assert T, 'Lemma T: no terminal'
    Ux = U[x]
    order = sorted(bits(Ux), key=lambda h: -I.v[x][h]); p = order[0]

    def adm_x(A): return I.admissible(x, A, Ux)

    def swap(t, A):
        b2 = list(Bs); b2[t] = gm; b2[x] = A; b2 = tuple(b2)
        assert b2 in kp.S, ('Lemma 6: the swap is not a min-frozen state', lst(Bs), t, sorted(bits(A)))
        return b2

    def admissibles(G):
        return [mask(c) for r in (1, 2) for c in itertools.combinations(list(bits(G & Ux)), r) if adm_x(mask(c))]

    # (F1): W_t threatens x for every free t
    for o in free:
        W = Bs[o] | J
        assert I.threat(x, W, I.v[x][g]), '(F1) violated: W_o spares x but def(P) >= 1'

    def thb(t):          # P-level theta-b: 4 goods, base = its two best lower goods, third lower good in J, big-top
        return pc(I.R[t]) == 4 and bigtop_on(I, t, g) and pc(Bs[t]) == 2 and not (U[t] & ~(Bs[t] | J))

    # Case 1: a terminal t with theta_t(J ∪ B_t) <= v_t(g); x owns J ∪ B_t
    for t in T:
        G = J | Bs[t]
        if not I.threat(t, G, I.v[t][g]):
            assert not thb(t) or pc(G) == 3, 'Case 1 at a theta-b terminal with |G| >= 4'
            A = admissibles(G)
            assert A, '(F1): no admissible set for x inside J ∪ B_t'
            b2 = swap(t, A[0])
            assert kp.D[b2] <= 0, ('Case 1 fails', d, lst(Bs), t)
            return '1'
    assert all(thb(t) for t in T), 'a terminal outside Case 1 that is not theta-b'
    # Case 2: S >= 1: x owns (J ∪ B_t) minus one lower good of t
    if S >= 1:
        t = T[0]; G = J | Bs[t]
        A = admissibles(G)[0]
        c = next(iter(bits(U[t] & ~A)))
        b2 = swap(t, A)
        assert kp.D[b2] <= 0, ('Case 2 fails', d, lst(Bs), t)
        return '2'
    assert om >= 2
    # Case 3 (S = 0): every free agent holds a pair, J is the pool
    if len(T) == 1:
        t = T[0]; G = J | Bs[t]
        A = admissibles(G)[0]
        b2 = swap(t, A) if U[t] & ~Ux else swap(t, mask(order[:2]))
        assert kp.D[b2] <= 0, ('Case 3 (one terminal) fails', d, lst(Bs))
        return '3x' if U[t] & ~Ux else '3x='
    # C-pair (Lemma C at the state level): A admissible, robust for x, meeting U_t or of one good
    for t in T:
        G = J | Bs[t]
        for A in admissibles(G):
            if I.val(x, A) < I.val(x, Ux & ~A): continue
            if not (A & U[t]) and pc(A) != 1: continue
            b2 = swap(t, A)
            assert kp.D[b2] <= 0, ('Case 3C fails', d, lst(Bs), t, sorted(bits(A)))
            return '3C'
    if len(T) == 2:
        for t in T:
            G = J | Bs[t]
            for A in admissibles(G):
                if pc(A) == 2 and I.val(x, A) > I.v[x][g]:
                    b2 = swap(t, A)
                    assert kp.D[b2] <= 0, ("Case 3C' fails", d, lst(Bs), t, sorted(bits(A)))
                    return "3C'"
        cnt['AR residual (E)'] += 1
        ex.setdefault('residual (E)', (d, k, lst(Bs)))
        return 'E'
    # |T| >= 3: A = {p} with p in J and v_x(D minus p) <= v_x(p), owner another terminal
    D = J & Ux
    if D & (1 << p) and I.val(x, D & ~(1 << p)) <= I.v[x][p]:
        b2 = swap(T[0], 1 << p)
        assert kp.D[b2] <= 0, ('Case 3p fails', d, lst(Bs))
        return '3p'
    cnt['AR residual R3'] += 1
    ex.setdefault('residual R3', (d, k, lst(Bs)))
    return 'R3'


# ------------------------------------------------------------------------------------------------ implementation B
def indep_check(d, kp, zmA):
    """main's repo-free k4/rt4_n5_indep.py: deficits, def* and zm at every state of every key with def* > 0"""
    import rt4_n5_indep as R
    ns = R.analyse(d['sets'], d['vals'], d['m'])
    assert ns['f'] == kp.I.f, ('indep f', ns['f'], kp.I.f)
    tob = lambda Pt: tuple(mask(B) for B in Pt)
    DB = {tob(Pt): v for Pt, v in ns['D'].items()}
    INF = float('inf')
    assert set(DB) == set(kp.D), 'indep: the min-frozen classes differ'
    for b, v in DB.items():
        assert (kp.D[b] >= 10 ** 9 and v == INF) or v == kp.D[b], ('indep deficit', lst(b), v, kp.D[b])
    mf = ns['mf']; info = ns['info']; classify = ns['classify']
    checked = 0
    for b, z in zmA.items():
        Pt = tuple(frozenset(bits(B)) for B in b)
        zB = any(ns['D'][Q] <= 0 and 'T3+' in classify(Pt, Q)[0] for Q in mf)
        assert zB == z, ('indep zm', lst(b), zB, z)
        checked += 1
    return checked


# ------------------------------------------------------------------------------------------------ driver
def read(args):
    for a in args:
        if a.startswith('inst:'):
            fn = a[5:]
            L = json.load(gzip.open(fn, 'rt') if fn.endswith('.gz') else open(fn))
            for e in L:
                yield {'sets': e['sets'], 'vals': e['vals'], 'm': e.get('m') or 1 + max(map(max, e['sets']))}
        else:
            for line in gzip.open(a, 'rt'):
                r = json.loads(line)
                yield {'sets': r['sets'], 'vals': r['vals'], 'm': r['m']}


def run_profile(d, opt, cnt, ex, do_indep):
    kp = KeyProfile(d)
    if not kp.ok: return
    I = kp.I
    if I.f > opt['fmax']: return
    cnt['profiles f=%d' % I.f] += 1
    zmA = {}
    for k in kp.K:
        if kp.dstar[k] <= 0: continue
        cnt['keys f=%d' % I.f] += 1
        cl, rob, U = key_classes(kp, k)
        nfree = sum(1 for y in range(I.n) if k[y] is None)
        cnt["keys f=%d: free agents not robust at the Z'-maxima = %d" % (I.f, nfree - max(rob[b] for b in cl['RLAM']))] += 1
        for b in kp.K[k]:
            if b not in zmA: zmA[b] = bool(zm_moves(kp, b))
        for name in CLASSES:
            L = cl[name]
            bad = [b for b in L if not zmA.get(b, None)] if name != 'TRL' else \
                [b for b in L if not (zmA[b] if b in zmA else bool(zm_moves(kp, b)))]
            cnt['%-8s states' % name] += len(L)
            cnt['%-8s states without zm' % name] += len(bad)
            if bad:
                cnt['%-8s keys with a state without zm' % name] += 1
                ex.setdefault(name, (d, k, lst(bad[0])))
            if L and len(bad) == len(L):
                cnt['%-8s keys where NO state of the class has zm' % name] += 1
        if not any(zmA[b] for b in cl['RLAM']):
            t4 = any(kp.dstar[keyof(kp.PA[b2])] < kp.dstar[k] for b in kp.K[k] for b2 in kp.t4_moves(b))
            cnt['ZMOVE FAILS at the key (no Z\'-maximum has zm); T4 edge %s' % t4] += 1
            print('ZMOVE-FAIL', json.dumps(d), k, 'T4 edge', t4, flush=True)
        if I.f >= 2:
            # k4/zmove_pot.md §6: does Theorem AR's conclusion (one move without helper) carry over to f >= 2?
            Uset = set(cl['U'])
            for b in kp.K[k]:
                if rob[b] != nfree or b not in Uset: continue
                mv = zm_moves(kp, b)
                cnt["f=%d states, every free agent robust and locally optimal: zm %s, without helper %s, plain (T3) "
                    "without helper %s" % (I.f, bool(mv), any(h is None for b2, x, z, W, h in mv),
                                           any(h is None and not W for b2, x, z, W, h in mv))] += 1
        if I.f == 1:
            x = next(i for i in range(I.n) if k[i] is not None); gm = 1 << k[x]
            free = [y for y in range(I.n) if y != x]
            for b in kp.K[k]:
                P = kp.PA[b]
                if rob[b] != len(free): continue
                T = [z for z in free if P.N[z] & gm]
                if not all(locally_optimal(I, P, t) for t in T): continue
                case = theorem_ar(kp, k, b, cnt, ex, d)
                cnt['AR states: case %s' % case] += 1
                cnt['AR states: case %s, Z\'-max %s' % (case, b in set(cl['RLAM']))] += 1
    if do_indep:
        cnt['indep profiles'] += 1
        cnt['indep states (zm compared)'] += indep_check(d, kp, zmA)


def main(argv):
    if not argv: print(__doc__); return
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    files = [a for a in argv if not a.startswith('--')]
    every = int(opt.get('every', 1)); indep = int(opt.get('indep', 0)); mx = int(opt.get('max', 10 ** 9))
    o = {'fmax': int(opt.get('fmax', 99))}
    print('# command: python3 k4/zmove_pot.py ' + ' '.join(argv), flush=True)
    cnt = collections.Counter(); ex = {}; seen = set(); j = 0; t0 = time.time()
    for d in read(files):
        kk = json.dumps([d['sets'], d['vals'], d['m']])
        if kk in seen: continue
        seen.add(kk); j += 1
        if (j - 1) % every: continue
        if cnt['profiles read'] >= mx: break
        cnt['profiles read'] += 1
        run_profile(d, o, cnt, ex, indep and (cnt['profiles read'] - 1) % indep == 0)
        if time.time() - t0 > float(opt.get('tmax', 1e12)): cnt['STOPPED at tmax'] += 1; break
    for k in sorted(cnt): print('%-72s %d' % (k, cnt[k]))
    for name, (d, k, b) in sorted(ex.items()):
        print('EX %-14s %s key %s state %s' % (name, json.dumps({'sets': d['sets'], 'vals': d['vals'], 'm': d['m']}), list(k), b))
    print('# time %.1f s' % (time.time() - t0))


if __name__ == '__main__':
    main(sys.argv[1:])
