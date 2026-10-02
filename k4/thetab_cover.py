#!/usr/bin/env python3
"""Case (i) of K4.SX.COVER (k4/sx.md §5 item 2, PR #80): Theorem Z′'s configurations at a non-completable f = 1 key in
which every terminal leaf is θ-b (workstream proof/k4-thetab; k4/thetab.md §7). EVIDENCE tooling.

Setting and notation of k4/sx.md §1-§3 (PR #80): f = 1, a key κ = (g, x) with def*(κ) > 0, Q a Z′-maximum (maximizes
(r', Λ') over the configurations at κ), X_o = Q_o ∪ L, V the leaves (free agents threatening no free agent), T the
terminals (free agents needing g at P_Q), θ-b(o): ω >= 2, o has four goods, is big-top on g and U_o ⊆ X_o.
*Case (i)*: V ∩ T is nonempty and every agent of V ∩ T is θ-b (so Lemma A applies to no terminal leaf).

At every Z′-maximum in case (i) the tool records:
  - the shape: |T|, |V ∩ T|, terminals outside V, |V|, n, ω, whether setting (H) of k4/thetab.md holds at P_Q;
  - when T = {τ1, τ2} ⊆ V: Lemma P of k4/thetab.md §7 (Lemma C's pair for τ1 or τ2, else Lemma C′'s pair, else the
    exception (E)); its criterion and its conclusion are asserted against a brute-force search;
  - Lemma C (k4/sx.md): for some θ-b terminal leaf τ1 and leaf o != τ1, whether a pair P_x ⊆ X_τ1 for x exists that
    is robust for x and meets U_τ1 ('pair'), and then whether (H*) / the exact (H) hold; why it fails otherwise
    ('no other leaf', 'no robust pair meeting U_τ1', '(H) fails');
  - Lemma C′: whether T = {τ1, τ2} ⊆ V, a robust pair worth more than g inside X_τ1, a w with U_τ2 ⊆ Y, and (H′*) / (H′);
  - Lemma B (k = 1) or B′ from a terminal outside V (k4/sx_zprime.gpm_check);
  - Theorems W, K and Corollary G1 of k4/thetab.md at P_Q (k4/thetab_lib.theorems: the first of W, K, G1 (plain
    swap), G1h (one helper) whose hypotheses hold; conclusions def(P') <= 0 asserted against exact deficits);
  - whether some (T3) move from P_Q reaches deficit <= 0 (exact).
Per key: covered by C or C′ (structural / exact), by B or B′ with k = 1, by W, K, G1, G1h at some Z′-maximum.
Smallest Z′-maximum (by n, m) per failing cell is printed.

Needs PR #80's k4/sx_keygraph.py and k4/sx_zprime.py (on main) and its dumps under results/k4_sx/; nothing of
PR #80 is changed. They are imported only when keys are analysed, so --sum runs without them.
usage: python3 k4/thetab_cover.py DUMP.jsonl.gz ... [--every=E] [--start=S] [--max=N]
       python3 k4/thetab_cover.py --sum results/k4_thetab/cover_*.log        (the table of k4/thetab.md §7)"""
import collections, gzip, itertools, json, os, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, 'suite'))
from thetab_lib import *                                         # noqa: E402,F401
Z = None                                                         # PR #80's k4/sx_zprime.py, imported by load_sx()


def load_sx():
    global Z
    if Z is None:
        import sx_zprime
        Z = sx_zprime
    return Z


def thetab_of(I, o, g, U, X, om):
    return Z.bigtop_on(I, o, g) and not (U[o] & ~X[o]) and om >= 2


def lemma_c(I, c, x, g, U, X, V, T, VT, free, om):
    """Lemma C's hypotheses at Q: returns (status, detail) with status 'C' (structural (H*)), 'Cx' (exact (H) only),
    or the reason it fails"""
    reasons = set()
    best = None
    for t1 in VT:
        if not thetab_of(I, t1, g, U, X, om): continue
        others = [o for o in V if o != t1]
        if not others: reasons.add('no other leaf'); continue
        pairs = c_pairs(I, x, U, X, t1)
        p = max(bits(U[x]), key=lambda h: I.v[x][h])
        crit = bool(U[x] & X[t1] & U[t1]) or (bool(X[t1] >> p & 1) and I.v[x][p] >= I.val(x, U[x] & ~(1 << p)))
        assert crit == bool(pairs), 'the criterion of Lemma P (i) for C-pairs'
        if not pairs: reasons.add('no robust pair meeting U_tau1'); continue
        for o in others:
            for Px in pairs:
                Y = c.Q[o] | (X[t1] & ~Px)
                hstar = not any(I.R[y] & c.Q[t1] & ~Px for y in free if y not in (o, t1))
                hexact = not any(I.threat(y, Y, c.hv(y)) for y in free if y not in (o, t1))
                if hstar: return 'C', None
                if hexact: best = 'Cx'
                else: reasons.add('(H) fails')
    if best: return best, None
    return 'C fails: ' + ', '.join(sorted(reasons)), None


def lemma_c2(I, c, x, g, U, X, V, T, free, om):
    """Lemma C′ of k4/sx.md (PR #80, as reviewed): exactly two terminals, τ1 θ-b (not necessarily a leaf), τ2 a leaf"""
    if len(T) != 2: return "C' fails: not exactly two terminals"
    reasons = set(); best = None
    for t1 in T:
        t2 = next(z for z in T if z != t1)
        if t2 not in V: reasons.add('the other terminal is not a leaf'); continue
        if not thetab_of(I, t1, g, U, X, om): reasons.add('tau1 not theta-b'); continue
        pairs = []
        for pr in itertools.combinations(list(bits(X[t1])), 2):
            Px = mask(pr)
            if not (Px & U[x] and I.admissible(x, Px & U[x], U[x])): continue
            if I.val(x, Px) < I.val(x, U[x] & ~Px) or I.val(x, Px) <= I.v[x][g]: continue
            pairs.append(Px)
        if not pairs: reasons.add('no robust pair worth more than g'); continue
        for Px in pairs:
            ws = [w for w in bits(U[t1] & ~Px) if not (U[t2] & ~((X[t2] | c.Q[t1]) & ~Px & ~(1 << w)))]
            if not ws: reasons.add('U_tau2 not inside Y'); continue
            for w in ws:
                Y = (X[t2] | c.Q[t1]) & ~Px & ~(1 << w)
                hstar = not any(I.R[y] & c.Q[t1] & ~Px & ~(1 << w) for y in free if y not in (t1, t2))
                hexact = not any(I.threat(y, Y, c.hv(y)) for y in free if y not in (t1, t2))
                if hstar: return "C'"
                if hexact: best = "C'x"
                else: reasons.add("(H') fails")
    if best: return best
    return "C' fails: " + (', '.join(sorted(reasons)) or 'no theta-b terminal')


def c_pairs(I, x, U, X, t1):
    """Lemma C's pairs (brute force): P ⊆ X_t1 with P ∩ U_x admissible for x, robust for x, meeting U_t1"""
    out = []
    for pr_ in itertools.combinations(list(bits(X[t1])), 2):
        Px = mask(pr_)
        if not (Px & U[x] and I.admissible(x, Px & U[x], U[x])): continue
        if I.val(x, Px) < I.val(x, U[x] & ~Px) or not Px & U[t1]: continue
        out.append(Px)
    return out


def c2_pairs(I, c, x, g, U, X, t1, t2):
    """Lemma C′'s pairs (brute force): P ⊆ X_t1, admissible and robust for x, worth more than g, with some
    w ∈ U_t1 ∖ P such that U_t2 ⊆ (X_t2 ∪ Q_t1) ∖ (P ∪ {w})"""
    out = []
    for pr_ in itertools.combinations(list(bits(X[t1])), 2):
        Px = mask(pr_)
        if not (Px & U[x] and I.admissible(x, Px & U[x], U[x])): continue
        if I.val(x, Px) < I.val(x, U[x] & ~Px) or I.val(x, Px) <= I.v[x][g]: continue
        if any(not (U[t2] & ~((X[t2] | c.Q[t1]) & ~Px & ~(1 << w))) for w in bits(U[t1] & ~Px)): out.append(Px)
    return out


def lemma_p(I, c, x, g, U, X, t1, t2):
    """Lemma P of k4/thetab.md §7 at a Z′-maximum with T = {t1, t2} ⊆ V, both θ-b: returns 'C-pair' (Lemma C's pair
    for t1 or t2), "C'-pair only" or '(E)'; the criterion of the proof is asserted against the brute-force search,
    and (E) against the absence of both pairs"""
    p = max(bits(U[x]), key=lambda h: I.v[x][h])
    crit = {}
    for a in (t1, t2):
        S = U[x] & X[a]
        crit[a] = bool(S & U[a]) or (bool(X[a] >> p & 1) and I.v[x][p] >= I.val(x, U[x] & ~(1 << p)))
        assert crit[a] == bool(c_pairs(I, x, U, X, a)), ('Lemma P: the criterion for C-pairs', a)
    cp = crit[t1] or crit[t2]
    c2p = bool(c2_pairs(I, c, x, g, U, X, t1, t2)) or bool(c2_pairs(I, c, x, g, U, X, t2, t1))
    vs = sorted((I.v[x][h] for h in bits(U[x])), reverse=True)
    E = (pc(U[x]) == 3 and not (U[x] & ~c.L) and not (U[x] & (U[t1] | U[t2]))
         and I.v[x][g] > vs[0] + vs[1] and vs[0] < vs[1] + vs[2])
    assert cp or c2p or E, 'Lemma P violated: no pair and not (E)'
    assert not (E and (cp or c2p)), 'Lemma P: (E) with a pair'
    return 'C-pair' if cp else ("C'-pair only" if c2p else '(E)')


def analyse(kp, pr, k, cnt, ex, src):
    I = kp.I
    x = next(i for i in range(I.n) if k[i] is not None); g = k[x]; gm = 1 << g
    free = [i for i in range(I.n) if i != x]
    U = {y: I.R[y] & ~gm for y in range(I.n)}
    cs = I.configs([k])
    lev = lambda c: sum(I.level(y, c.Q[y] & I.R[y]) for y in free)
    rob = lambda c: sum(1 for y in free if c.robust(y))
    best = max((rob(c), lev(c)) for c in cs)
    mx = [c for c in cs if (rob(c), lev(c)) == best]
    ds = kp.dstar[k]; om = I.omega
    nb = None
    keyc = set(); in_case = False
    for c in mx:
        Bs = tuple(gm if i == x else (c.Q[i] & U[i]) for i in range(I.n))
        P = kp.PA[Bs]
        X = {o: c.Q[o] | c.L for o in free}
        V = [o for o in free if not any(I.threat(y, X[o], c.hv(y)) for y in free if y != o)]
        T = [z for z in free if P.N[z] & gm]
        VT = [o for o in V if o in T]
        if not VT or not all(thetab_of(I, o, g, U, X, om) for o in VT): continue
        in_case = True
        cnt['case (i) Z′-maxima'] += 1
        ctx = Ctx(pr, Bs)
        H = in_H(ctx)
        shape = 'n=%d omega=%d |T|=%d |VT|=%d |V|=%d T outside V=%d (H)=%s' % (
            I.n, om, len(T), len(VT), len(V), len(T) - len(VT), H)
        cnt['shape ' + shape] += 1
        lp = '-'
        if len(T) == 2 and set(T) <= set(V):
            lp = lemma_p(I, c, x, g, U, X, T[0], T[1])
            cnt['Lemma P (T = two theta-b leaves): ' + lp] += 1
        cst, _ = lemma_c(I, c, x, g, U, X, V, T, VT, free, om)
        c2 = lemma_c2(I, c, x, g, U, X, V, T, free, om)
        if nb is None: nb = kp.neighbours()
        gc = Z.gpm_check(kp, k, c, V, T, X, nb['T3'][k], collections.Counter(), collections.defaultdict(list), 0, 'x')
        b = 'B1' if 'B1' in gc else ("B1'" if "B1'" in gc else ("B1'x" if "B1'x" in gc else 'no B1'))
        thm = theorems(pr, ctx, src)
        direct = any(kp.D[m[0]] <= 0 for m in kp.t3plus_moves(Bs) if not m[3])
        cnt['Lemma C: ' + cst] += 1
        cnt["Lemma C': " + c2] += 1
        cnt['Lemma B (k = 1): ' + b] += 1
        cnt['k4/thetab.md at P_Q: first of W, K, G1, G1h: ' + thm] += 1
        cnt['a (T3) move from P_Q to deficit <= 0: %s' % direct] += 1
        sx = 'C' if cst == 'C' else ("C'" if c2 == "C'" else ('B1' if b in ('B1', "B1'") else (
            'Cx' if cst == 'Cx' else ("C'x" if c2 == "C'x" else ("B1'x" if b == "B1'x" else 'none')))))
        cnt['cell: sx lemma %s | thetab %s | (H) %s' % (sx, thm, H)] += 1
        keyc.add(sx)
        if thm != '-': keyc.add('thetab ' + thm)
        cell = ('|T|=%d |VT|=%d' % (len(T), len(VT)), lp, cst, c2, b, sx, thm)
        cand = (I.n, I.m, src, kp.d, k, repr(c), 'V', V, 'T', T)
        if cell not in ex or cand[:2] < ex[cell][:2]: ex[cell] = cand
        assert direct or thm == '-', 'a theorem applied but no (T3) move to deficit <= 0'
    if in_case:
        cnt['case (i) keys'] += 1
        struct = keyc & {'C', "C'", 'B1'}
        exact = keyc & {'C', "C'", 'B1', 'Cx', "C'x", "B1'x"}
        cnt['case (i) keys: some maximum covered by C, C′ or B1 (structural hypotheses) = %s' % bool(struct)] += 1
        cnt['case (i) keys: some maximum covered by C, C′ or B1 (exact hypotheses) = %s' % bool(exact)] += 1
        for t in ('W', 'K', 'G1', 'G1h'):
            if 'thetab ' + t in keyc:
                cnt['case (i) keys: some maximum covered by k4/thetab.md, first %s' % t] += 1; break
        else:
            cnt['case (i) keys: no maximum covered by k4/thetab.md'] += 1
        cnt['case (i) keys: some maximum covered by C, C′, B1 (exact) or k4/thetab.md = %s' % bool(keyc - {'none'})] += 1


def summary(files):
    """the table of k4/thetab.md §7 from the logs of this tool"""
    import re
    rows = []; tot = collections.Counter()
    for fn in files:
        c = collections.Counter()
        for l in open(fn):
            m = re.match(r'\s+(.*?)\s+(\d+)$', l)
            if m: c[m.group(1)] += int(m.group(2))
        sh = collections.Counter()
        for k, v in c.items():
            if k.startswith('shape '):
                t = re.search(r'\|T\|=(\d+) \|VT\|=(\d+)', k)
                sh['two leaves' if t.groups() == ('2', '2') else ('one leaf' if t.group(2) == '1' else 'other')] += v
        c.update({'S ' + k: v for k, v in sh.items()})
        rows.append((os.path.basename(fn).replace('.log', ''), c)); tot.update(c)
    rows.append(('**total**', tot))
    print('| input | keys / maxima | T two θ-b leaves / one θ-b leaf + a non-leaf terminal / other | Lemma P: C-pair / '
          "C′-pair only / (E) | C / C′ / B (k = 1), structural hypotheses (maxima) | keys: some maximum by C, C′, B "
          '(structural / exact only) | first of W / K / G1 / G1h / none (maxima) |')
    print('|---|---|---|---|---|---|---|')
    for name, c in rows:
        print('| %s | %d / %d | %d / %d / %d | %d / %d / %d | %d / %d / %d | %d / %d | %s |' % (
            name, c['case (i) keys'], c['case (i) Z′-maxima'], c['S two leaves'], c['S one leaf'], c['S other'],
            c['Lemma P (T = two theta-b leaves): C-pair'], c["Lemma P (T = two theta-b leaves): C'-pair only"],
            c['Lemma P (T = two theta-b leaves): (E)'], c['Lemma C: C'], c["Lemma C': C'"],
            c['Lemma B (k = 1): B1'] + c["Lemma B (k = 1): B1'"],
            c['case (i) keys: some maximum covered by C, C′ or B1 (structural hypotheses) = True'],
            c['case (i) keys: some maximum covered by C, C′ or B1 (exact hypotheses) = True']
            - c['case (i) keys: some maximum covered by C, C′ or B1 (structural hypotheses) = True'],
            ' / '.join(str(c['k4/thetab.md at P_Q: first of W, K, G1, G1h: ' + t]) for t in ('W', 'K', 'G1', 'G1h', '-'))))


def main(argv):
    if argv and argv[0] == '--sum': return summary(argv[1:])
    print('# command: python3 k4/thetab_cover.py ' + ' '.join(argv), flush=True)
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    rest = [a for a in argv if not a.startswith('--')]
    profs = []
    for fn in rest:
        for line in gzip.open(fn, 'rt'):
            r = json.loads(line)
            if r.get('f', 1) == 1: profs.append(({'sets': r['sets'], 'vals': r['vals'], 'm': r['m']}, r.get('src', fn)))
    profs = profs[int(opt.get('start', 0))::int(opt.get('every', 1))]
    if 'max' in opt: profs = profs[:int(opt['max'])]
    cnt = collections.Counter(); ex = {}; t0 = time.time()
    load_sx()
    for d, src in profs:
        kp = Z.KeyProfile(d)
        if not kp.ok or kp.I.f != 1: continue
        cnt['profiles'] += 1
        pr = None
        for k in kp.K:
            if kp.dstar[k] <= 0: continue
            cnt['non-completable keys'] += 1
            if pr is None: pr = Profile(d)
            analyse(kp, pr, k, cnt, ex, src)
    for k in sorted(cnt): print('  %-110s %d' % (k, cnt[k]))
    print('smallest Z′-maximum per cell (shape, Lemma P, Lemma C, Lemma C′, Lemma B, first sx lemma, first of k4/thetab.md):')
    for cell, v in sorted(ex.items(), key=str):
        print('  %s: n=%d m=%d %s %s key=%s %s %s' % (cell, v[0], v[1], v[2], json.dumps(v[3]), list(v[4]), v[5],
                                                      ' '.join(map(str, v[6:]))))
    print('no assertion failed; time %.0f s' % (time.time() - t0), flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
