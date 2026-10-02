#!/usr/bin/env python3
"""Lemmas C⁺, C′⁺ and Cx⁺ of k4/f2.md §5 (the f >= 2 analogues of k4/sx.md Lemmas C and C′, PR #80, from Theorem Z′'s
state P_Q), tested at every maximum of (r′, Λ′) where PR #80's Lemmas A⁺ and B⁺ do not apply (workstream
proof/k4-f2). EVIDENCE tooling for written proofs.

Inputs, read as PR #80's k4/sx_f2.py reads them (k4/ and results/k4_sx/ on main once PR #80 is merged; before that, copies of proof/k4-sx at de4ee31 in
k4/suite/.cache/sx/, k4/f2.md §8):
  cat   results/k4_sx/chunks/{gap_n4_3_s4000@f2e1,gap_n4_pure_s4000@f2e1,hard_hunt@f2e1,hunt_n4_3_s400k@f2e1,
        hunt_n4_pure_s400k@f2e1}_c000.jsonl.gz and gap_n4_1_c0{00..11}.jsonl.gz          (67 keys, 49 uncovered)
  stuck results/k4_sx/t3stage/keys.jsonl.gz                                            (196 keys, 40 uncovered)
  n5c   --inst=results/k4_sx/f2/rt4_n5c_inst.json                                      (26 keys, 7 uncovered)
For every key κ with def*(κ) > 0, PR #80's k4/sx_f2.analyse_key (imported unchanged; its assertions of Lemmas F⁺, A⁺,
B⁺ run) lists the maxima Q of (r′, Λ′) at κ where neither A⁺ nor B⁺ applies (*uncovered maxima*). At each, from
P_Q (frozen w on {φ(w)}, free y on H_y = Q_y ∩ U_y, X_y = Q_y ∪ L), for every frozen x, every need path
τ = a_{k+1}, a_k, ..., a_1, x from a free τ (k4/f2.md §3.1) and every admissible A ⊆ (J ∪ H_τ) ∩ R_x, the move P′
(τ takes φ(a_k), a_i takes φ(a_{i-1}), x takes A; Lemma 6⁺: a (T3) move for k = 0, no helper) and:
  C⁺   o ≠ τ free, off the path; P_x ⊆ X_τ a pair for x with P_x ∩ U_x = A; Y := Q_o ∪ (X_τ \\ P_x) (|Y| = ω + 2);
       hypotheses (a) θ_x(Y) <= v_x(A), (b) θ_τ(Y) <= v_τ(φ(a_k)), (c) Y threatens no agent outside {o, τ, x} holding
       its P_Q base. Conclusion asserted: def(P′) <= 0. Also recorded: (a*) P_x robust for x; (H*) X_o threatens
       nobody outside {o, x} and no agent outside {x, o, τ} values a good of Q_τ \\ P_x (each implies its letter).
  C′⁺  o ≠ τ free, off the path; Y a bundle of o in P′ (H_o ⊆ Y ⊆ H_o ∪ J(P′)) with |Y| = ω + 1 and (a), (b), (c);
       (ι1) every agent that needs φ(x) in P_Q is o or a_1 (a_1 := τ for k = 0): no third needer;
       (ι2) φ(x) ∉ N_o(Y); (ι3) v_x(A) > v_x(φ(x)). Conclusion asserted: def(P′) <= 0.
  Cx⁺  the owner is x: Z ⊆ J ∪ H_τ with |Z| = ω + 1, (i′) v_x(Z) > v_x(φ(x)), (ii) Z threatens no agent outside
       {τ, x} holding its P_Q base, (iii) θ_τ(Z) <= v_τ(φ(a_k)), (ι1′) no agent other than τ needs φ(a_k) in P_Q;
       A ranges over the admissible subsets of Z ∩ R_x (one exists). Conclusion asserted: def(P′) <= 0.
At the maxima where C′⁺ or Cx⁺ fails only by (ι1)/(ι1′), the third needers are recorded (frozen or free).
usage: python3 k4/f2_cc.py NAME [--inst=FILE.json] [DUMP.jsonl.gz ...]"""
import collections, gzip, itertools, json, os, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from f2_lib import Prof, bits, pc, mask, kind, lst
from f2_lemmas import Ctx
sys.path.append(os.path.join(HERE, 'suite', '.cache', 'sx', 'k4'))
import sx_f2                                    # PR #80's tool, unchanged (k4/suite/.cache/sx/k4/sx_f2.py)
from sx_keygraph import KeyProfile, keyof


def keyprofile(pr):
    """PR #80's KeyProfile on the min-frozen class already computed by Prof (same model.py, same deficits)"""
    kp = KeyProfile.__new__(KeyProfile)
    kp.I, kp.d, kp.ok = pr.I, pr.d, pr.ok
    kp.mp = pr.mp; kp.S = set(pr.mp); kp.PA = pr.PA; kp.D = pr.D
    kp.K = collections.defaultdict(list)
    for Bs in pr.mp: kp.K[keyof(pr.PA[Bs])].append(Bs)
    kp.dstar = {k: min(pr.D[b] for b in v) for k, v in kp.K.items()}
    return kp


def maxima(kp, k):
    """the maxima of (r′, Λ′) at k, as in sx_f2.analyse_key: [(c, Bs, leaves, {o: X_o})]"""
    I = kp.I
    free = [i for i in range(I.n) if k[i] is None]
    Nm = mask(k[i] for i in range(I.n) if k[i] is not None)
    U = {y: I.R[y] & ~Nm for y in range(I.n)}
    cs = I.configs([k])
    lev = lambda c: sum(I.level(y, c.Q[y] & I.R[y]) for y in free)
    rob = lambda c: sum(1 for y in free if c.robust(y))
    best = max((rob(c), lev(c)) for c in cs)
    out = []
    for c in cs:
        if (rob(c), lev(c)) != best: continue
        Bs = tuple((1 << k[i]) if k[i] is not None else (c.Q[i] & U[i]) for i in range(I.n))
        X = {o: c.Q[o] | c.L for o in free}
        V = [o for o in free if not any(I.threat(y, X[o], c.hv(y)) for y in free if y != o)]
        out.append((c, Bs, V, X))
    return out


def acyclic(pr, k):
    """the frozen need digraph of the key k (w -> w′ when w, on its good, needs the good of w′) has no cycle"""
    I = pr.I
    mk = tuple((1 << k[i]) if k[i] is not None else 0 for i in range(I.n))
    P0 = pr.PA[pr.bykey[mk][0]]
    F = [i for i in range(I.n) if k[i] is not None]
    succ = {w: [v for v in F if v != w and P0.N[w] & (1 << k[v])] for w in F}
    st = {}

    def cyc(u):
        st[u] = 1
        for v in succ[u]:
            if st.get(v) == 1 or (v not in st and cyc(v)): return True
        st[u] = 2
        return False
    return not any(w not in st and cyc(w) for w in F)


def subsets(pool, k):
    return (mask(S) for S in itertools.combinations(list(bits(pool)), k))


def counted(pr, P, Bs, o, Y, path, A, x):
    """Fact 3 (k4/f2.md §5): the goods q of 𝒩 that are counted in u′_o(Y) after the chain swap along path with x
    taking A (no helper) by the sufficient conditions (1) q ∉ N_o(Y); (2) every agent that needs q in P is o or the
    agent holding q in P′; (3) o = x or q ∉ N_x(A). Each is asserted to be counted (exact P′ needs)."""
    I = pr.I
    hold = {path[j]: Bs[path[j + 1]] for j in range(len(path) - 1)}; hold[x] = A
    holder = {}
    for i in range(I.n):
        B = hold.get(i, Bs[i])
        if pc(B) == 1 and B & P.NA: holder[B] = i
    NoY = I.needs(o, Y); NxA = I.needs(x, A)
    out = []
    for q in bits(P.NA):
        qb = 1 << q
        if NoY & qb: continue
        if any(P.N[i] & qb for i in range(I.n) if i not in (o, holder[qb])): continue
        if o != x and NxA & qb: continue
        # exact: nobody but o needs q in P′, and o does not need it given Y
        assert not any(I.needs(i, hold.get(i, Bs[i])) & qb for i in range(I.n) if i != o), ('Fact 3', Bs, q)
        out.append(q)
    return out


def test_max(pr, c, Bs, V, X, cnt, ex):
    """Lemmas C+ and C′+ at P_Q = Bs; returns (the set of (lemma, k, ...) that apply, obstruction counter)"""
    I = pr.I; ctx = Ctx(pr, Bs); P = ctx.P; om = ctx.omega
    assert om == I.omega and pc(c.L) == om
    U = {y: I.R[y] & ~P.NA for y in range(I.n)}
    thr = lambda w, Z, B: I.threat(w, Z, I.val(w, B))
    applied = set(); why = collections.Counter()
    for x in ctx.F:
        gx = Bs[x]
        for path in ctx.paths_to(x):
            tau = path[0]; k = len(path) - 2; gk = Bs[path[1]]
            onpath = set(path)
            G = P.J | Bs[tau]
            Xt = X[tau]
            assert not (Xt & ~G)
            for A in ctx.adm(x, G):
                b2 = ctx.swap(path, A)
                assert b2 in pr.D, ('Lemma 6+', Bs, b2)
                D2 = pr.D[b2]
                hold = ctx.hold(path); hold[x] = A
                Jn = G & ~A
                # ---------------------------------------------------------------- C+ (Y = Q_o ∪ (X_τ minus P_x))
                for Px in subsets(Xt, 2):
                    if Px & U[x] != A: continue
                    for o in P.free:
                        if o in onpath: continue
                        Y = c.Q[o] | (Xt & ~Px)
                        assert pc(Y) == om + 2 and not (Y & ~(Bs[o] | Jn))
                        ha = not thr(x, Y, A); hb = not thr(tau, Y, gk)
                        hc = not any(thr(w, Y, Bs[w]) for w in range(I.n) if w not in (o, tau, x))
                        astar = I.val(x, Px) >= I.val(x, U[x] & ~Px)
                        hstar = (not any(thr(w, X[o], Bs[w]) for w in range(I.n) if w not in (o, x))
                                 and not any(I.R[w] & c.Q[tau] & ~Px for w in range(I.n) if w not in (x, o, tau)))
                        if astar: assert ha, 'C+: (a*) without (a)'
                        if hstar: assert hc, 'C+: (H*) without (c)'
                        if ha and hb and hc:
                            assert D2 <= 0, ('Lemma C+', Bs, b2, D2)
                            applied.add(('C+', k, 'owner a leaf' if o in V else 'owner not a leaf',
                                         '(a*)' if astar else 'not (a*)', '(H*)' if hstar else 'not (H*)'))
                            if ex is not None: ex.append(('C+', k, o, tau, x))
                # ---------------------------------------------------------------- C′+ (any owner, any bundle)
                for o in [x] + [o for o in P.free if o not in onpath]:
                    base = A if o == x else Bs[o]
                    for sz in (om + 1, om + 2):
                        if sz < pc(base): continue
                        for K in subsets(Jn & ~base, sz - pc(base)):
                            Y = base | K
                            others = [w for w in range(I.n) if w not in (o, tau, x)]
                            safe = (not thr(tau, Y, gk) and (o == x or not thr(x, Y, A))
                                    and not any(thr(w, Y, Bs[w]) for w in others))
                            if not safe: continue
                            assert not any(thr(w, Y, hold.get(w, Bs[w])) for w in range(I.n) if w != o), 'Fact 1'
                            role = 'owner x' if o == x else ('owner a leaf' if o in V else 'owner not a leaf')
                            if sz == om + 2:          # Lemma H1 alone: a safe bundle of ω + 2 goods
                                assert D2 <= 0, ('full bundle', Bs, b2, D2)
                                applied.add(('full', k, role))
                                if ex is not None: ex.append(('full', k, o, tau, x))
                                continue
                            qs = counted(pr, P, Bs, o, Y, path, A, x)
                            if qs:
                                assert D2 <= 0, ("Lemma C′+", Bs, b2, D2)
                                kinds = sorted(set('phi(x)' if (1 << q) == gx else
                                                   ('phi(a_k), now tau\'s' if (1 << q) == gk else
                                                    'phi(w) of a frozen w off the move') for q in qs))
                                applied.add(("C'+", k, role, '+'.join(kinds)))
                                if ex is not None: ex.append(("C'+", k, o, tau, x))
                            else:
                                third = [i for i in range(I.n) if P.N[i] & gx and i not in (o, path[-2])]
                                why[("C'+: Y safe, |Y| = omega+1, no good counted by Fact 3",
                                     'def(P′) <= 0' if D2 <= 0 else 'def(P′) > 0',
                                     'third needers of phi(x): ' + (','.join('frozen' if P.frozen[i] else 'free'
                                                                            for i in third) or 'none'))] += 1
    return applied, why


FAMILIES = [   # restricted families of k4/f2.md §5 (the f = 1 mechanisms alone, and the full lemmas)
    ('C+', lambda a: a[0] == 'C+'),
    ("C'+", lambda a: a[0] == "C'+"),
    ("C'+ with q = phi(x)", lambda a: a[0] == "C'+" and 'phi(x)' in a[3]),
    ('C+ or (C′+ with q = phi(x))', lambda a: a[0] == 'C+' or (a[0] == "C'+" and 'phi(x)' in a[3])),
    ('(C+ with (H*)) or (C′+ with q = phi(x))', lambda a: (a[0] == 'C+' and a[4] == '(H*)') or
     (a[0] == "C'+" and 'phi(x)' in a[3])),
    ('C+ or C′+', lambda a: a[0] in ('C+', "C'+")),
    ('C+ or C′+ with k = 0 (plain (T3), no helper)', lambda a: a[0] in ('C+', "C'+") and a[1] == 0)]


def main(argv):
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    rest = [a for a in argv if not a.startswith('--')]
    name, files = rest[0], rest[1:]
    print('# command: python3 k4/f2_cc.py ' + ' '.join(argv), flush=True)
    profs = []
    if 'inst' in opt:
        fi = opt['inst']
        profs = [{'sets': d['sets'], 'vals': d['vals'], 'm': d['m']}
                 for d in json.load(gzip.open(fi, 'rt') if fi.endswith('.gz') else open(fi))]
    for fn in files:
        for line in gzip.open(fn, 'rt'):
            r = json.loads(line)
            if r['f'] >= 2: profs.append({'sets': r['sets'], 'vals': r['vals'], 'm': r['m']})
    cnt = collections.Counter(); t0 = time.time(); smallest = {}
    for d in profs:
        pr = Prof(d, fmin=2)
        if not pr.ok: continue
        kp = keyprofile(pr)
        cnt['profiles f=%d' % pr.I.f] += 1
        for k in kp.K:
            if kp.dstar[k] <= 0: continue
            c1 = collections.Counter(); exs = collections.defaultdict(list)
            sx_f2.analyse_key(kp, k, c1, exs, 10 ** 6)
            cnt['keys def*>0'] += 1
            cnt[('keys', 'frozen need digraph ' + ('acyclic' if acyclic(pr, k) else 'cyclic (Proposition NK)'),
                 'A+ or B+ (PR #80)' if c1['keys: Lemma A+ or B+ at some Zmax=True'] else 'C+ or C′+ needed')] += 1
            if c1['keys: Lemma A+ or B+ at some Zmax=True']:
                cnt['keys covered by A+ or B+ (PR #80)'] += 1; continue
            cnt['keys uncovered by A+ and B+'] += 1
            unc = set(e[2] for e in exs['noAplus'])
            keyres = set()
            for c, Bs, V, X in maxima(kp, k):
                if repr(c) not in unc: continue
                cnt['uncovered maxima'] += 1
                inst = []
                applied, why = test_max(pr, c, Bs, V, X, cnt, inst)
                # roles (k4/f2.md §7, What remains): x threatened by a leaf? tau a leaf? the owner the leaf that threatens x?
                thrl = {o: set(w for w in range(pr.I.n) if w != o and pr.PA[Bs].frozen[w]
                               and pr.I.threat(w, X[o], pr.I.val(w, Bs[w]))) for o in V}
                sigs = set()
                for lem, kk, o, tau, x in inst:
                    lem = "C'+" if lem == "C'+" else 'C+'
                    xs = 'x threatened by a leaf' if any(x in thrl[l] for l in V) else 'x threatened by no leaf'
                    ts = 'tau a leaf' if tau in V else 'tau not a leaf'
                    os_ = ('owner x' if o == x else 'owner a leaf threatening x' if o in V and x in thrl[o]
                           else 'owner a leaf not threatening x' if o in V else 'owner not a leaf')
                    sigs.add((lem, xs, ts, os_))
                    sigs.add(('any', xs, ts))
                for sg in sigs: cnt[('uncovered maxima', 'roles') + sg] += 1
                names = set(a[0] for a in applied)
                keyres |= names
                for nm in ('C+', 'full', "C'+"):
                    if nm in names:
                        cnt[('uncovered maxima', nm + ' applies', 'least k=%d' % min(a[1] for a in applied
                                                                                 if a[0] == nm))] += 1
                for a in set(a[:1] + a[2:] for a in applied):
                    cnt[('uncovered maxima', 'kinds') + a] += 1
                for fam, test in FAMILIES:
                    hit = any(test(a) for a in applied)
                    cnt[('uncovered maxima', 'covered by the family', fam, hit)] += 1
                    if not hit:
                        szk = (pr.I.n, pr.I.m, sum(map(sum, d['vals'])))
                        cur = smallest.get('not covered by ' + fam)
                        if cur is None or szk < cur[0]:
                            smallest['not covered by ' + fam] = (szk, d, k, repr(c), lst(Bs), kp.dstar[k], pr.D[Bs],
                                                                sorted(map(str, applied)))
                lk = min(a[1] for a in applied) if applied else None
                cnt[('uncovered maxima', 'least k over the lemmas that apply', lk)] += 1
                for nm in ('C+', 'full', "C'+"):
                    for a in applied:
                        if a[0] != nm: continue
                        szk = (pr.I.n, pr.I.m, sum(map(sum, d['vals'])))
                        tg = 'k=%d %s' % (a[1], ' '.join(map(str, a[:1] + a[2:])))
                        cur = smallest.get(tg)
                        if cur is None or szk < cur[0]:
                            smallest[tg] = (szk, d, k, repr(c), lst(Bs), kp.dstar[k], pr.D[Bs], None)
                tag = 'C+' if 'C+' in names else ('full bundle, other form' if 'full' in names else
                                                  ("C'+" if names else 'none'))
                cnt[('uncovered maxima', 'first: ' + tag)] += 1
                cnt[('uncovered maxima', 'C+ or C′+ applies', bool(names))] += 1
                # obstruction triples (move, owner, bundle): a safe bundle of ω + 1 goods at which no good passes Fact 3
                tot = sum(why.values())
                third = sum(v for w, v in why.items() if not w[2].endswith('none'))
                frz = sum(v for w, v in why.items() if 'frozen' in w[2])
                frzpos = sum(v for w, v in why.items() if 'frozen' in w[2] and w[1] == 'def(P′) > 0')
                cnt[('obstruction', 'triples (safe bundle of omega+1 goods, no good passes Fact 3)')] += tot
                cnt[('obstruction', 'triples with a third needer of phi(x)')] += third
                cnt[('obstruction', 'maxima with such a triple')] += third > 0
                cnt[('obstruction', 'triples with a frozen third needer of phi(x)')] += frz
                cnt[('obstruction', 'maxima with such a triple (frozen)')] += frz > 0
                cnt[('obstruction', 'triples with a frozen third needer and def(P′) > 0')] += frzpos
                if not names:
                    szk = (pr.I.n, pr.I.m, sum(map(sum, d['vals'])))
                    cur = smallest.get('none')
                    if cur is None or szk < cur[0]:
                        smallest['none'] = (szk, d, k, repr(c), lst(Bs), kp.dstar[k], pr.D[Bs], dict(why))
            cnt[('uncovered keys', 'some maximum covered by C+ / C′+', bool(keyres))] += 1
            for nm in sorted(keyres): cnt[('uncovered keys', nm + ' at some maximum')] += 1
            if not keyres:
                szk = (pr.I.n, pr.I.m, sum(map(sum, d['vals'])))
                cur = smallest.get('key none')
                if cur is None or szk < cur[0]:
                    smallest['key none'] = (szk, d, k, None, None, kp.dstar[k], None, None)
    print('### %s' % name)
    for kk in sorted((k for k in cnt if cnt[k]), key=str):
        print('  %-120s %d' % (' | '.join(map(str, kk)) if isinstance(kk, tuple) else kk, cnt[kk]))
    for tag, v in sorted(smallest.items()):
        _, d, k, cr, B, ds, dq, why = v
        print('  smallest [%s]: n=%d m=%d sets=%s vals=%s key=%s def*=%d config=%s P_Q=%s def(P_Q)=%s why=%s' % (
            tag, len(d['sets']), d['m'], d['sets'], d['vals'], list(k), ds, cr, B, dq, why))
    print('# time %.1f s' % (time.time() - t0))
    print('# no assertion failed')


if __name__ == '__main__':
    main(sys.argv[1:])
