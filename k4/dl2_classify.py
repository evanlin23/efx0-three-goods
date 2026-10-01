#!/usr/bin/env python3
"""DL2 repair classification (workstream proof/k4-dl2-k1; k4/dl2.md, k4/strategy.md §3 "Next steps" step 2).

For every min-frozen P in the space 𝒫 of k4/c4x.md §1 with removal-only deficit def(P) > 0, record
  * the obstruction at P: the best owners o (free agents attaining def(P) in Lemma H1 of k4/hall.md §1:
    def(P) = omega + 2 - max(|X| + u_o(X)) over free o and safe X, B_o ⊆ X ⊆ W_o = B_o ∪ J), an optimal X and its
    removed set C = J \\ X (a minimum hitting set of o's threat hypergraph in the Lemma H1 sense), and for every agent x
    exposed w.r.t. o (W_o threatens x holding B_x) its class:
      free x:   e1 / e2 / e3 (the exact shapes of Lemma H3), or fU (x violates (U): at most one base good and a junk
                good of R_x), fU2 (x violates (U2): a better pair in B_x ∪ (R_x ∩ J)), fO (none of these);
      frozen x: G / G1 / L (Lemma H7, with the plain G test and the chain-end test of k4/gap.md §0), or O (none);
      a frozen x exposed w.r.t. two or more free agents is also tagged '2' (the double threat of Lemma D,
      k4/c4min_reduce.md §3);
  * the minimal repairs: every min-frozen P' with def(P') < def(P) at the least distance k(P) (number of agents whose
    base changes), each with a type string (which agents change, their roles at P, how their bases change).
Everything is computed with k4/suite/model.py (the suite's own transcription of k4/c4x.md §1); the deficit of every
min-frozen P is recomputed here from Lemma H1 and asserted equal to model.Inst.deficit.

usage:
  python3 k4/dl2_classify.py suite [--out=FILE]                     every suite instance with omega >= 1, n <= 6
  python3 k4/dl2_classify.py catalog FILE [--every=E] [--max=N] [--jobs=J] [--out=FILE]
  python3 k4/dl2_classify.py one '{"sets": ..., "vals": ...}'        one profile, verbose
Output: one JSON line per def > 0 state (gzip if FILE ends in .gz); the table is made by k4/dl2_table.py."""
import gzip, itertools, json, os, sys
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'suite'))
import model as M
from model import bits, pc, mask

INF = 10 ** 9


# ------------------------------------------------------------------ basic objects of a pre-allocation
class PA:
    """a pre-allocation P (bases Bs) of instance I with its needs, junk, frozen agents and slots"""

    def __init__(self, I, Bs):
        self.I, self.Bs, n = I, tuple(Bs), I.n
        self.N = [I.needs(i, Bs[i]) for i in range(n)]
        NA = 0
        for x in self.N: NA |= x
        self.NA = NA
        used = 0
        for B in Bs: used |= B
        self.J = I.ALL & ~used
        self.frozen = [pc(Bs[i]) == 1 and bool(Bs[i] & NA) for i in range(n)]
        self.free = [i for i in range(n) if not self.frozen[i]]
        self.S = sum(0 if self.frozen[i] else 2 - pc(Bs[i]) for i in range(n))
        self.bv = [I.val(i, Bs[i]) for i in range(n)]

    def safe(self, o, X):
        I = self.I
        return not any(I.threat(x, X, self.bv[x]) for x in range(I.n) if x != o)

    def u(self, o, X):
        """agents frozen in P that are not frozen once o's needs are taken from X (Lemma H1)"""
        I = self.I
        NA2 = I.needs(o, X)
        for j in range(I.n):
            if j != o: NA2 |= self.N[j]
        return sum(1 for j in range(I.n) if j != o and self.frozen[j] and not (self.Bs[j] & NA2))

    def owner_best(self, o):
        """max over safe X (B_o ⊆ X ⊆ B_o ∪ J) of |X| + u_o(X), and the optimal X's (maximal by inclusion first)"""
        Jl = list(bits(self.J)); B = self.Bs[o]
        best, arg = -1, []
        for k in range(len(Jl), -1, -1):
            for K in itertools.combinations(Jl, k):
                X = B | mask(K)
                if not self.safe(o, X): continue
                val = pc(X) + self.u(o, X)
                if val > best: best, arg = val, [X]
                elif val == best: arg.append(X)
        return best, arg

    def deficit(self):
        """(def, {o: (best, [X...])}); def = omega + 2 - max(|X| + u) by Lemma H1 (INF if no free agent)"""
        omega = pc(self.J) - self.S
        if omega <= 0: return omega, {}
        res = {o: self.owner_best(o) for o in self.free}
        if not res: return INF, res
        mx = max(b for b, _ in res.values())
        return omega + 2 - mx, res

    def W(self, o): return self.Bs[o] | self.J


# ------------------------------------------------------------------ classes of exposures
def sorted_goods(I, i):
    return sorted(I.sets[i], key=lambda g: -I.v[i][g])


def chain_ends(P, x):
    """free agents reached from frozen x along need edges (y -> z when B_y = {g}, g ∈ N_z) through frozen agents"""
    I = P.I; seen = {x}; stack = [x]; ends = set()
    while stack:
        y = stack.pop()
        if pc(P.Bs[y]) != 1: continue
        for z in range(I.n):
            if z in seen or not (P.N[z] & P.Bs[y]): continue
            seen.add(z)
            if P.frozen[z]: stack.append(z)
            else: ends.add(z)
    return ends


def bigtop(I, x):
    if len(I.sets[x]) != 4: return False
    a, b, c, d = [I.v[x][g] for g in sorted_goods(I, x)]
    return a > b + c


def violates_U(P, x):
    """(U) / (U2) of Lemma H2 for a free agent x: 'fU', 'fU2' or None"""
    I = P.I; B = P.Bs[x]; RJ = I.R[x] & P.J
    if pc(B) <= 1:
        return 'fU' if RJ else None
    v = P.bv[x]
    for A in itertools.combinations(list(bits(B | RJ)), 2):
        if I.val(x, mask(A)) > v: return 'fU2'
    return None


def exposure_class(P, o, x):
    """class of the exposure of x w.r.t. owner o (W_o threatens x holding B_x)"""
    I = P.I; B = P.Bs[x]; Bo = P.Bs[o]; J = P.J; R = I.R[x]
    if not P.frozen[x]:
        if pc(B) == 1 and not (R & J) and pc(Bo) == 2 and not (Bo & ~(R & ~B)):
            return 'e1'
        if len(I.sets[x]) == 4 and pc(B) == 2:
            a, b, c, d = sorted_goods(I, x)
            va = I.v[x]
            if B == mask([b, c]) and (Bo >> a) & 1 and (J >> d) & 1 and va[a] + va[d] > va[b] + va[c]:
                return 'e2'
            if not (R & J) and (R & ~B) == Bo:
                return 'e3'
        return violates_U(P, x) or 'fO'
    g = next(bits(B)); vg = I.v[x][g]
    RJ = R & J
    if pc(RJ) >= 2 and I.val(x, RJ) > vg:
        return 'G'
    ce = chain_ends(P, x)
    if o in ce:
        a = sorted_goods(I, x)[0]
        if bigtop(I, x) and g == a and not (R & ~(1 << a) & ~(J | Bo)):
            return 'G1'
        return 'O'
    if I.val(x, R & J) <= vg:
        return 'L'
    return 'O'


def labels(P, o, x):
    """least number of junk goods whose removal from W_o protects x, and whether x is unhittable (only by keeping
    at most two goods, i.e. |X| <= 2)"""
    I = P.I; W = P.W(o); Jl = list(bits(P.J)); Bo = P.Bs[o]
    for k in range(len(Jl) + 1):
        for K in itertools.combinations(Jl, k):
            X = W & ~mask(K)
            if not I.threat(x, X, P.bv[x]):
                return k, pc(X) <= 2
    return None, True


# ------------------------------------------------------------------ the profile
def roles(P, o, exposed):
    """role letter of each agent at P w.r.t. owner o"""
    I = P.I; out = []
    for i in range(I.n):
        if i == o: out.append('o')
        elif P.frozen[i]: out.append('X' if i in exposed else 'F')
        elif i in exposed: out.append('x')
        elif P.N[i] & P.NA: out.append('n')      # a free needer (terminal) of a frozen good
        else: out.append('-')
    return out


def change(P, P2, i, other):
    """how agent i's base changes from P to P2: e.g. 'f>f:+J-J^' ; other = the set of other changed agents"""
    B, B2 = P.Bs[i], P2.Bs[i]
    add, drop = B2 & ~B, B & ~B2
    src = ''
    for g in bits(add):
        if P.J >> g & 1: src += '+J'
        elif any(P.Bs[j] >> g & 1 for j in other): src += '+T'
        else: src += '+?'
    for g in bits(drop):
        if P2.J >> g & 1: src += '-J'
        elif any(P2.Bs[j] >> g & 1 for j in other): src += '-T'
        else: src += '-?'
    st = ('F' if P.frozen[i] else 'f') + '>' + ('F' if P2.frozen[i] else 'f')
    v, v2 = P.bv[i], P2.bv[i]
    arrow = '^' if v2 > v else ('v' if v2 < v else '=')
    return st + ':' + (src or '0') + arrow


def repair_type(P, P2, o, exposed):
    ch = [i for i in range(P.I.n) if P.Bs[i] != P2.Bs[i]]
    rl = roles(P, o, exposed)
    parts = []
    for i in ch:
        oth = [j for j in ch if j != i]
        parts.append(rl[i] + '[' + change(P, P2, i, oth) + ']')
    return ' '.join(sorted(parts))


def analyze(d, want_repairs=True, maxrep=6):
    """list of records, one per min-frozen P with def(P) > 0"""
    I = M.Inst(d['sets'], d['vals'], d.get('m'))
    I.preallocs()
    if I.omega <= 0: return [], {'omega': I.omega, 'f': I.f, 'nmin': len(I.minP)}
    mp = [Bs for Bs, NA in I.minP]
    PAs = {Bs: PA(I, Bs) for Bs in mp}
    D, OWN = {}, {}
    for Bs in mp:
        dv, res = PAs[Bs].deficit()
        ref = I.deficit(Bs)
        ref = INF if ref is None else ref
        assert dv == ref, ('deficit mismatch', Bs, dv, ref)
        D[Bs], OWN[Bs] = dv, res
    # Pareto-maximality inside the min-frozen class (a Pareto improvement of a min-frozen P is min-frozen)
    vec = {Bs: tuple(PAs[Bs].bv) for Bs in mp}
    recs = []
    for Bs in mp:
        if D[Bs] <= 0: continue
        P = PAs[Bs]
        res = OWN[Bs]
        mx = max((b for b, _ in res.values()), default=None)
        best = sorted(o for o, (b, _) in res.items() if b == mx) if mx is not None else []
        pareto = not any(all(a >= b for a, b in zip(vec[B2], vec[Bs])) and vec[B2] != vec[Bs] for B2 in mp)
        obs = []
        for o in best:
            W = P.W(o)
            exp = [x for x in range(I.n) if x != o and I.threat(x, W, P.bv[x])]
            cls = {}
            for x in exp:
                c = exposure_class(P, o, x)
                if P.frozen[x]:
                    mult = sum(1 for o2 in P.free if o2 != x and I.threat(x, P.W(o2), P.bv[x]))
                    if mult >= 2: c += '2'
                lab, unh = labels(P, o, x)
                cls[x] = (c, lab, unh)
            X = res[o][1][0]
            obs.append({'o': o, 'X': sorted(bits(X)), 'C': sorted(bits(P.J & ~X)), 'u': P.u(o, X),
                        'exp': {str(x): list(v) for x, v in cls.items()}})
        rec = {'Bs': [sorted(bits(B)) for B in Bs], 'def': D[Bs], 'f': I.f, 'omega': I.omega,
               'frozen': [i for i in range(I.n) if P.frozen[i]], 'J': sorted(bits(P.J)), 'pareto': pareto,
               'best': best, 'obs': obs}
        if want_repairs:
            dist = None; reps = []
            for B2 in mp:
                if D[B2] >= D[Bs]: continue
                k = sum(1 for a, b in zip(Bs, B2) if a != b)
                if dist is None or k < dist: dist, reps = k, [B2]
                elif k == dist: reps.append(B2)
            rec['k'] = dist
            o0 = obs[0]['o'] if obs else None
            exp0 = set(int(x) for x in obs[0]['exp']) if obs else set()
            rr = []
            for B2 in reps:
                P2 = PAs[B2]
                mx2 = max(b for b, _ in OWN[B2].values()) if OWN[B2] else None
                best2 = sorted(o for o, (b, _) in OWN[B2].items() if b == mx2) if mx2 is not None else []
                rr.append({'Bs': [sorted(bits(B)) for B in B2], 'def': D[B2], 'best': best2,
                           'type': repair_type(P, P2, o0, exp0)})
            rr.sort(key=lambda r: (r['def'], r['type']))
            rec['nrep'] = len(rr)
            rec['types'] = sorted(set(r['type'] for r in rr))
            rec['reps'] = rr[:maxrep]
        recs.append(rec)
    return recs, {'omega': I.omega, 'f': I.f, 'nmin': len(mp)}


def one_record(args):
    d, src = args
    try:
        recs, info = analyze(d)
    except AssertionError as e:
        return src, d, None, {'error': str(e)}
    return src, d, recs, info


def opener(fn):
    return gzip.open(fn, 'wt') if fn.endswith('.gz') else open(fn, 'w')


def main(argv):
    if not argv: print(__doc__); return
    mode = argv[0]; rest = [a for a in argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) for a in argv[1:] if a.startswith('--') and '=' in a)
    every = int(opt.get('every', 1)); mx = int(opt['max']) if 'max' in opt else None
    jobs = int(opt.get('jobs', 1)); out = opt.get('out')
    items = []
    if mode == 'suite':
        import glob
        for f in sorted(glob.glob(os.path.join(HERE, 'suite', 'instances', '*.json'))):
            d = json.load(open(f))
            if 'kind' in d or len(d['sets']) > int(opt.get('nmax', 6)): continue
            d.setdefault('m', 1 + max(g for S in d['sets'] for g in S))
            items.append(({'sets': d['sets'], 'vals': d['vals'], 'm': d['m']}, d['id']))
    elif mode == 'catalog':
        cat = rest[0]
        recs = json.load(gzip.open(cat, 'rt'))['records'][::every]
        if mx: recs = recs[:mx]
        base = os.path.basename(cat).replace('.json.gz', '')
        for r in recs:
            c = r['core']
            items.append(({'sets': c['sets'], 'vals': r['vals'], 'm': c['m']},
                          '%s:%s#%d:%s' % (base, c['file'], c['idx'], ','.join(map(str, r['prof'])))))
    elif mode == 'one':
        d = json.loads(rest[0]); recs, info = analyze(d)
        print(json.dumps(info))
        for r in recs: print(json.dumps(r))
        return
    else:
        print(__doc__); return
    print('# command: python3 k4/dl2_classify.py ' + ' '.join(argv), flush=True)
    fo = opener(out) if out else None
    nprof = nstate = nerr = 0
    hist = {}
    it = map(one_record, items) if jobs <= 1 else Pool(jobs).imap(one_record, items, chunksize=4)
    for src, d, recs, info in it:
        nprof += 1
        if recs is None:
            nerr += 1; print('ERROR', src, info, flush=True); continue
        for r in recs:
            nstate += 1
            hist[r.get('k')] = hist.get(r.get('k'), 0) + 1
            if fo:
                r2 = dict(r); r2['src'] = src; r2['sets'] = d['sets']; r2['vals'] = d['vals']; r2['m'] = d['m']
                fo.write(json.dumps(r2, separators=(',', ':')) + '\n')
        if mode == 'suite':
            print('%-40s n=%d omega=%s f=%s minP=%s def>0: %d  k: %s' % (
                src, len(d['sets']), info.get('omega'), info.get('f'), info.get('nmin'), len(recs),
                sorted(set(r.get('k') for r in recs), key=lambda x: (x is None, x))), flush=True)
    if fo: fo.close()
    print('profiles %d, def>0 states %d, errors %d, k histogram %s' % (
        nprof, nstate, nerr, dict(sorted(hist.items(), key=lambda x: (x[0] is None, x[0] or 0)))), flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
