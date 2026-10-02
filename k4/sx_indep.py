#!/usr/bin/env python3
"""Referee's independent check of k4/sx.md (PR #80) at f = 1. Written independently in the PR #80 review; shares no
repository code (workstream proof/k4-sx commits it unchanged except for this docstring and the "# command" / "# time"
lines of main). EVIDENCE tooling. Written from the raw definitions only:
c4x.md §1 (𝒫, needs, frozen, removal-only deficit by direct enumeration of C ⊆ J, no Lemma H1), c4min.md §1
(configurations, valid owner with C and unfreezing), dl2.md §3 / sx.md §1 ((T3) move shape). Shares no code with the
repository.

For every f = 1 profile given, every key (g, x), every configuration at the key:
  - Lemma 0: def*(κ) <= 0 iff some configuration at κ is completable;
  - at every Z'-maximum of a non-completable key: Lemma F (forest, in-degree, robust roots, V = leaves, V threatens x,
    kinds), Theorem Z' (V nonempty);
  - at EVERY pool-optimal configuration (the lemmas only assume pool-optimality): Lemma S, Lemma A, Lemma B (all paths,
    all k), Lemma B' (exact (H_B') and (H_B'*)), Lemma C ((H) and (H*)), Lemma C' ((H') and (H'*)), each for every
    choice of x's pair: the target state is in 𝒫 with one frozen agent, the claimed key, def <= 0 (raw), and for the
    single-move cases the move is (T3) by the definition;
  - COVER at every non-completable key (some Z'-max with A, B1, B1', C or C').

usage: python3 k4/sx_indep.py DUMP.jsonl.gz|INST_inst.json [MAX [START]]   (lines "V ..." are violations or notes)
"""
import itertools, json, gzip, sys, random, collections, time

def F(*a): return frozenset(a)

class Prof:
    def __init__(s, sets, vals, m):
        s.n = len(sets); s.m = m
        s.R = [frozenset(S) for S in sets]
        s.v = [dict(zip(S, V)) for S, V in zip(sets, vals)]
        s.M = frozenset(range(m))
        s._dcache = {}
    def val(s, i, Z): return sum(s.v[i].get(h, 0) for h in Z)
    def theta(s, i, Z):
        if not Z: return 0
        return max(s.val(i, Z - {h}) for h in Z)
    def needs(s, i, B):
        vb = s.val(i, B)
        return frozenset(h for h in s.R[i] - B if s.v[i][h] > vb)
    # ---- 𝒫 (c4x.md §1)
    def info(s, P):
        """None if P is not in 𝒫, else (NA, frozen set, J)"""
        used = set()
        for i, B in enumerate(P):
            if len(B) > 2 or not B <= s.R[i] or used & B: return None
            used |= B
        N = [s.needs(i, B) for i, B in enumerate(P)]
        NA = frozenset().union(*N)
        J = s.M - used
        if J & NA: return None
        if any(len(B) == 2 and B & NA for B in P): return None
        Fr = frozenset(i for i, B in enumerate(P) if len(B) == 1 and B <= NA)
        assert len(Fr) == len(NA)
        return NA, Fr, J
    def all_states(s):
        opts = []
        for i in range(s.n):
            R = sorted(s.R[i])
            o = [frozenset()] + [F(a) for a in R] + [F(a, b) for a, b in itertools.combinations(R, 2)]
            opts.append(o)
        out = []
        def rec(i, used, cur):
            if i == s.n:
                P = tuple(cur)
                inf = s.info(P)
                if inf is not None: out.append((P, inf))
                return
            for B in opts[i]:
                if B & used: continue
                cur.append(B); rec(i + 1, used | B, cur); cur.pop()
        rec(0, frozenset(), [])
        return out
    def deficit(s, P):
        """removal-only deficit, c4x.md §1, by enumeration of C ⊆ J"""
        if P in s._dcache: return s._dcache[P]
        NA, Fr, J = s.info(P)
        S = sum(2 - len(P[i]) for i in range(s.n) if i not in Fr)
        om = len(J) - S
        if om <= 0:
            s._dcache[P] = om; return om
        best = None
        Jl = sorted(J)
        N = [s.needs(i, P[i]) for i in range(s.n)]
        for o in range(s.n):
            if o in Fr: continue
            Nother = frozenset().union(*[N[i] for i in range(s.n) if i != o])
            for r in range(len(Jl) + 1):
                for C in itertools.combinations(Jl, r):
                    X = P[o] | (J - set(C))
                    if any(s.theta(w, X) > s.val(w, P[w]) for w in range(s.n) if w != o): continue
                    vX = s.val(o, X)
                    NoX = frozenset(h for h in s.R[o] - X if s.v[o][h] > vX)
                    NA2 = Nother | NoX
                    So = sum(2 - len(P[i]) for i in range(s.n) if i != o and not (len(P[i]) == 1 and P[i] <= NA2))
                    d = len(C) - So
                    if best is None or d < best: best = d
        s._dcache[P] = best
        return best

def is_T3(pr, P, P2, infP, infP2):
    NA, Fr, _ = infP; NA2, Fr2, _ = infP2
    if NA != NA2: return False, 'NA changed'
    ch = [i for i in range(pr.n) if P[i] != P2[i]]
    xs = [i for i in ch if i in Fr and i not in Fr2]
    zs = [i for i in ch if i not in Fr and i in Fr2]
    if len(xs) != 1 or len(zs) != 1: return False, 'x/z count %s %s' % (xs, zs)
    x, z = xs[0], zs[0]
    if P2[z] != P[x] or not P[x] <= pr.needs(z, P[z]): return False, 'z does not take a needed B_x'
    if any(i in Fr and i in Fr2 for i in ch): return False, 'frozen in both'
    rest = [i for i in ch if i not in (x, z)]
    if len(rest) > 1: return False, 'more than one helper: %s' % rest
    for h in rest:
        if h in Fr or h in Fr2: return False, 'helper not free'
        if P[h] <= P2[h]: return False, 'helper gives up nothing'
    return True, 'ok'

class Key:
    def __init__(s, pr, g, x, omega):
        s.pr, s.g, s.x, s.om = pr, g, x, omega
        s.Mp = pr.M - {g}
        s.U = [pr.R[y] - {g} for y in range(pr.n)]
        s.free = [y for y in range(pr.n) if y != x]
    def adm(s, y, A):
        U = s.U[y]
        if not A or len(A) > 2 or not A <= U: return False
        va = s.pr.val(y, A)
        return all(s.pr.v[y][h] < va for h in U - A)
    def pair_ok(s, y, Q): return s.adm(y, Q & s.U[y])
    def configs(s):
        Ml = sorted(s.Mp)
        cand = {y: [F(a, b) for a, b in itertools.combinations(Ml, 2) if s.pair_ok(y, F(a, b))] for y in s.free}
        out = []
        def rec(i, used, cur):
            if i == len(s.free):
                L = s.Mp - used
                assert len(L) == s.om
                out.append((dict(cur), L)); return
            y = s.free[i]
            for Q in cand[y]:
                if Q & used: continue
                cur[y] = Q; rec(i + 1, used | Q, cur); del cur[y]
        rec(0, frozenset(), {})
        return out

class Cfg:
    def __init__(s, K, Q, L):
        s.K, s.Q, s.L = K, Q, L
        pr = K.pr
        s.H = {y: Q[y] & K.U[y] for y in K.free}; s.H[K.x] = F(K.g)
        s.hv = {y: pr.val(y, s.H[y]) for y in range(pr.n)}
        s.X = {o: Q[o] | L for o in K.free}
    def robust(s, y): return s.K.pr.val(y, s.Q[y]) >= s.K.pr.val(y, s.K.U[y] - s.Q[y])
    def level(s, y):
        pr = s.K.pr; vH = s.hv[y]; R = sorted(pr.R[y])
        return sum(1 for r in range(len(R) + 1) for T in itertools.combinations(R, r) if pr.val(y, T) < vH)
    def pot(s): return (sum(s.robust(y) for y in s.K.free), sum(s.level(y) for y in s.K.free))
    def pool_opt(s):
        pr = s.K.pr
        for y in s.K.free:
            Z = sorted(s.Q[y] | s.L)
            vq = pr.val(y, s.Q[y])
            if any(pr.val(y, S) > vq for S in itertools.combinations(Z, 2)): return False
        return True
    def thr(s, Z, w): return s.K.pr.theta(w, Z) > s.hv[w]
    def state(s):
        return tuple(s.H[i] for i in range(s.K.pr.n))

def pairs_for_x(K, Z):
    """pairs Q'_x ⊆ Z whose part in U_x is admissible for x"""
    return [F(a, b) for a, b in itertools.combinations(sorted(Z), 2) if K.adm(K.x, F(a, b) & K.U[K.x])]

def kind(c, y):
    K = c.K; pr = K.pr
    if c.robust(y): return 'rob'
    gs = sorted(K.U[y], key=lambda h: -pr.v[y][h]); H = c.H[y]; v = pr.v[y]
    if len(pr.R[y]) == 3 and K.g not in pr.R[y] and H == F(gs[0]): return 'T3'
    if len(pr.R[y]) == 4 and K.g in pr.R[y] and H == F(gs[0]) and v[gs[0]] < v[gs[1]] + v[gs[2]]: return 'Tg'
    if len(pr.R[y]) == 4 and K.g not in pr.R[y]:
        a, b, cc, d = gs
        if H == F(a): return 'T4'
        if H == F(a, d) and v[a] + v[d] < v[b] + v[cc]: return 'D'
        if len(H) == 2 and a not in H:
            p, q = sorted(H); s4 = next(iter(K.U[y] - H - {a}))
            if v[p] + v[q] > v[a] and v[p] + v[q] < v[a] + v[s4]: return 'R'
    return '?'

def thetab(c, o):
    K = c.K; pr = K.pr
    if K.om < 2 or len(pr.R[o]) != 4 or K.g not in pr.R[o]: return False
    gs = sorted(K.U[o], key=lambda h: -pr.v[o][h])
    if not pr.v[o][K.g] > pr.v[o][gs[0]] + pr.v[o][gs[1]]: return False
    return K.U[o] <= c.X[o]

def owner_valid_C0(c2, o, keyx):
    """in configuration c2 (free agents c2.K.free, frozen keyx on g): o's bundle threatens nobody"""
    X = c2.X[o]
    return not any(c2.thr(X, w) for w in range(c2.K.pr.n) if w != o)

def completable(c):
    """c4min.md §1 valid-owner test with C (f = 1: only x can be unfrozen)"""
    K = c.K; pr = K.pr
    for o in K.free:
        X = c.X[o]
        for r in range(len(X) + 1):
            for C in itertools.combinations(sorted(X), r):
                Y = X - set(C)
                if not any(K.adm(o, A) for A in [F(h) for h in Y & K.U[o]] +
                           [F(a, b) for a, b in itertools.combinations(sorted(Y & K.U[o]), 2)]): continue
                if any(c.thr(Y, w) for w in range(pr.n) if w != o): continue
                vY = pr.val(o, Y)
                Ny = frozenset(h for h in pr.R[o] - Y if pr.v[o][h] > vY)
                other_need = any(K.g in pr.needs(y, c.H[y]) for y in K.free if y != o)
                unf = 0 if (other_need or K.g in Ny) else 1
                if len(C) <= unf: return True
    return False

cnt = collections.Counter()
viol = []

def V_(msg, *a):
    cnt['VIOLATION ' + msg] += 1
    if len(viol) < 30: viol.append((msg,) + a)

def check_target(pr, P, P2, tag, single, src_def):
    inf2 = pr.info(P2)
    if inf2 is None: V_(tag + ': target not in P', P2); return False
    if len(inf2[1]) != 1: V_(tag + ': target frozen count != 1', P2); return False
    d2 = pr.deficit(P2)
    if d2 > 0: V_(tag + ': target deficit > 0', P, P2, d2); return False
    if single:
        ok, why = is_T3(pr, P, P2, pr.info(P), inf2)
        if not ok: V_(tag + ': not a (T3) move: ' + why, P, P2); return False
    cnt[tag + ' ok'] += 1
    return True

def run_profile(d, deep=True):
    pr = Prof(d['sets'], d['vals'], d['m'])
    st = pr.all_states()
    f = min(len(inf[1]) for _, inf in st)
    if f != 1: cnt['skip f != 1'] += 1; return
    mins = [(P, inf) for P, inf in st if len(inf[1]) == 1]
    om = len(mins[0][1][2]) - sum(2 - len(mins[0][0][i]) for i in range(pr.n) if i not in mins[0][1][1])
    if om < 1: cnt['skip omega < 1'] += 1; return
    keys = collections.defaultdict(list)
    for P, inf in mins:
        x = next(iter(inf[1])); g = next(iter(P[x]))
        keys[(g, x)].append(P)
    cnt['profiles'] += 1
    for (g, x), Ps in keys.items():
        K = Key(pr, g, x, om)
        dstar = min(pr.deficit(P) for P in Ps)
        cfs = [Cfg(K, Q, L) for Q, L in K.configs()]
        # Lemma K: the configurations' states are exactly ... (check P_Q in the key)
        for c in cfs:
            inf = pr.info(c.state())
            if inf is None or inf[1] != F(x): V_('P_Q not a state of the key', c.state())
        comp = any(completable(c) for c in cfs)
        if comp != (dstar <= 0): V_('Lemma 0', d, (g, x), dstar, comp)
        cnt['keys'] += 1; cnt['keys def*>0'] += dstar > 0
        pots = [c.pot() for c in cfs]
        best = max(pots)
        covered = False
        for c, pt in zip(cfs, pots):
            zmax = pt == best
            po = c.pool_opt()
            if zmax and not po: V_("Theorem Z'(ii) pool-optimality", d, (g, x))
            if not po: continue
            cnt['pool-optimal configs'] += 1
            free = K.free
            out = {o: [w for w in free if w != o and c.thr(c.X[o], w)] for o in free}
            V = [o for o in free if not out[o]]
            T = [z for z in free if g in pr.R[z] and pr.val(z, c.Q[z]) < pr.v[z][g]]
            if not T: V_('Lemma T: no terminal', d)
            # Lemma F(a) kinds hold at every pool-optimal configuration
            indeg = collections.Counter(w for o in free for w in out[o])
            if any(indeg[w] > 1 for w in free): V_('two threateners', d)
            if any(indeg[w] for w in free if c.robust(w)): V_('robust threatened', d)
            kd = {y: kind(c, y) for y in free}
            if any(kd[y] == '?' for y in free): V_('kind ?', d, kd)
            if zmax and dstar > 0:
                cnt['Zmax of non-completable keys'] += 1
                # Lemma F
                if not V: V_("Theorem Z' V empty", d)
                if any(not c.thr(c.X[o], x) for o in V): V_('Lemma F(c): leaf spares x', d)
                if any(not (out[o] or c.thr(c.X[o], x)) for o in free): V_('Lemma F(c): agent threatens nobody', d)
                # acyclic
                col = {}
                def dfs(u):
                    col[u] = 1
                    for w in out[u]:
                        if col.get(w) == 1: V_('Lemma F(b): cycle', d)
                        elif w not in col: dfs(w)
                    col[u] = 2
                for u in free:
                    if u not in col: dfs(u)
            PQ = c.state()
            applies = set()
            # Lemma S
            for tau in T:
                for o in V:
                    if o != tau and not pr.theta(tau, c.X[o]) < pr.v[tau][g]: V_('Lemma S', d, (g, x), tau, o)
            # Lemma A
            for o in T:
                if o not in V or not c.thr(c.X[o], x) or thetab(c, o): continue
                prs = pairs_for_x(K, c.X[o])
                if not prs: V_('Lemma A: no pair for x', d)
                for Px in prs:
                    P2 = list(PQ); P2[o] = F(g); P2[x] = Px & K.U[x]; P2 = tuple(P2)
                    if check_target(pr, PQ, P2, 'Lemma A', True, dstar): applies.add('A')
            # Lemma B / B'
            for tau in T:
                paths = []
                def walk(u, path):
                    for w in out[u]:
                        if w in path: continue
                        if w in V: paths.append(path + [w])
                        walk(w, path + [w])
                walk(tau, [tau])
                for path in paths:
                    o = path[-1]; k = len(path) - 1
                    if not c.thr(c.X[o], x): continue
                    if kd[o] in ('rob', '?'): V_('Lemma B: leaf not of a threatened kind', d); continue
                    sL = False
                    if kd[o] == 'R':
                        a_o = max(K.U[o], key=lambda h: pr.v[o][h])
                        s_o = next(iter(K.U[o] - c.H[o] - {a_o}))
                        sL = s_o in c.L
                    if not sL:
                        prs = pairs_for_x(K, c.X[o])
                        if not prs: V_('Lemma B: no pair for x', d)
                        for Px in prs:
                            Qn = dict(c.Q)
                            for i in range(1, len(path)): Qn[path[i]] = c.Q[path[i - 1]]
                            del Qn[tau]; Qn[x] = Px
                            K2 = Key(pr, g, tau, om)
                            if any(not K2.pair_ok(y, Qn[y]) for y in Qn): V_('Lemma B: inadmissible', d); continue
                            c2 = Cfg(K2, Qn, c.X[o] - Px)
                            if not owner_valid_C0(c2, x, tau): V_('Lemma B: x not valid', d, (g, x), path, Px); continue
                            P2 = c2.state()
                            if check_target(pr, PQ, P2, 'Lemma B k=%d' % k, k == 1, dstar) and k == 1: applies.add('B1')
                    else:
                        y_ = next(iter(c.Q[path[-2]] - {a_o}))
                        if a_o not in c.Q[path[-2]]: V_("Lemma B': a not in predecessor's pair", d); continue
                        X2 = (c.X[o] - {s_o}) | {y_}
                        prs = pairs_for_x(K, X2)
                        cnt["Lemma B' X'' has a pair for x = %s (zmax %s, k=%d)" % (bool(prs), zmax and dstar > 0, k)] += 1
                        if not prs and len(viol) < 30: viol.append(("NOTE B' no pair for x", d, (g, x), dict(c.Q), sorted(c.L), path, zmax))
                        hstar = not any(y_ in pr.R[w] for w in range(pr.n) if w != x)
                        for Px in prs:
                            Qn = dict(c.Q)
                            for i in range(1, len(path)): Qn[path[i]] = c.Q[path[i - 1]]
                            del Qn[tau]; Qn[x] = Px; Qn[o] = F(a_o, s_o)
                            K2 = Key(pr, g, tau, om)
                            if any(not K2.pair_ok(y, Qn[y]) for y in Qn): V_("Lemma B': inadmissible", d); continue
                            c2 = Cfg(K2, Qn, X2 - Px)
                            hex_ = not any(c2.thr(X2, w) for w in range(pr.n) if w not in (x, o))
                            if hstar and not hex_: V_("Lemma B': (H_B'*) without (H_B')", d)
                            if not hex_: continue
                            if not owner_valid_C0(c2, x, tau): V_("Lemma B': x not valid", d, path, Px); continue
                            if check_target(pr, PQ, c2.state(), "Lemma B' k=%d" % k, k == 1, dstar) and k == 1:
                                applies.add("B1'")
            # Lemma C
            for t1 in T:
                if t1 not in V or not thetab(c, t1): continue
                for o in V:
                    if o == t1: continue
                    for Px in pairs_for_x(K, c.X[t1]):
                        if pr.val(x, Px) < pr.val(x, K.U[x] - Px) or not Px & K.U[t1]: continue
                        Y = c.Q[o] | (c.X[t1] - Px)
                        hstar = not any((c.Q[t1] - Px) & pr.R[w] for w in range(pr.n) if w not in (x, o, t1))
                        hex_ = not any(c.thr(Y, w) for w in free if w not in (o, t1))
                        if hstar and not hex_: V_('Lemma C: (H*) without (H)', d)
                        if not hex_: continue
                        Qn = dict(c.Q); del Qn[t1]; Qn[x] = Px
                        K2 = Key(pr, g, t1, om)
                        c2 = Cfg(K2, Qn, c.X[t1] - Px)
                        if not owner_valid_C0(c2, o, t1): V_('Lemma C: o not valid', d, (g, x), t1, o, Px); continue
                        if check_target(pr, PQ, c2.state(), 'Lemma C', True, dstar): applies.add('C')
            # Lemma C' (the statement: terminals exactly {t1, t2}, theta-b(t1), t2 threatens no free agent)
            if len(T) == 2:
                for t1 in T:
                    t2 = [z for z in T if z != t1][0]
                    if not thetab(c, t1) or t2 not in V: continue
                    for P_ in pairs_for_x(K, c.X[t1]):
                        if pr.val(x, P_) < pr.val(x, K.U[x] - P_) or not pr.val(x, P_) > pr.v[x][g]: continue
                        for w in K.U[t1] - P_:
                            Y = (c.X[t2] | c.Q[t1]) - P_ - {w}
                            if not K.U[t2] <= Y: continue
                            hstar = not any((c.Q[t1] - P_ - {w}) & pr.R[u] for u in range(pr.n) if u not in (x, t1, t2))
                            hex_ = not any(c.thr(Y, u) for u in free if u not in (t1, t2))
                            if hstar and not hex_: V_("Lemma C': (H'*) without (H')", d)
                            if not hex_: continue
                            P2 = list(PQ); P2[t1] = F(g); P2[x] = P_ & K.U[x]; P2 = tuple(P2)
                            cnt["Lemma C' t1 in V = %s" % (t1 in V)] += 1
                            if check_target(pr, PQ, P2, "Lemma C'", True, dstar): applies.add("C'")
            if zmax and dstar > 0:
                for a in applies: cnt['Zmax applies ' + a] += 1
                if applies: covered = True
                else: cnt['Zmax with none'] += 1
        if dstar > 0:
            cnt['COVER holds at key = %s' % covered] += 1
            if not covered and len(viol) < 30: viol.append(('COVER fails', d, (g, x)))

def main():
    args = sys.argv[1:]
    print('# command: python3 k4/sx_indep.py ' + ' '.join(args), flush=True)
    t0 = time.time()
    src = args[0]; mx = int(args[1]) if len(args) > 1 else 10**9; start = int(args[2]) if len(args) > 2 else 0
    profs = []
    if src.endswith('.jsonl.gz'):
        for line in gzip.open(src, 'rt'):
            r = json.loads(line); profs.append({'sets': r['sets'], 'vals': r['vals'], 'm': r['m']})
    elif src.endswith('inst.json'):
        for r in json.load(open(src)):
            profs.append({'sets': r['sets'], 'vals': r['vals'], 'm': r['m']} if 'vals' in r else r)
    elif src.startswith('random:'):
        # random:CERTS:per_core:seed
        _, fn, per, seed = src.split(':')
        rng = random.Random(int(seed))
        cores = json.load(gzip.open(fn, 'rt'))['cores']
        for c in cores:
            for _ in range(int(per)):
                vals = []
                for S in c['sets']:
                    while True:
                        vv = rng.sample(range(1, 13), len(S))
                        sums = [sum(t) for r in range(1, len(S) + 1) for t in itertools.combinations(vv, r)]
                        if len(set(sums)) == len(sums) and max(vv) < sum(vv) - max(vv): break
                    vals.append(vv)
                profs.append({'sets': c['sets'], 'vals': vals, 'm': c['m']})
    profs = profs[start:start + mx]
    for i, d in enumerate(profs):
        run_profile(d)
    for k in sorted(cnt): print('%-70s %d' % (k, cnt[k]))
    for v in viol: print('V', v)
    print('# time %.1f s' % (time.time() - t0))

if __name__ == '__main__':
    main()
