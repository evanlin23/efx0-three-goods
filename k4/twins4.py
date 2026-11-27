"""k = 4 minimal counterexample, round 3 (workstream proof/k4-twins): twins, near-twins and dense configurations.

Configurations (k4/MINCEX.md §2 notation; every interior good valued by exactly one agent of S is private to it):
  twins-<K>-<j>   two agents e, f of the same kind K in (Q3, Q4) with the same relevant set R; j goods of R are valued
                  by e and f only (interior, degree 2), the others are boundary goods;
  twins-P3        two P3 agents valuing the same two shared goods (k4/mincex4.py's twins_config; both boundary);
  near-<...>      two agents sharing 3 goods (see near_config);
  claw            three P3 agents sharing one good G of degree 3 (G interior), y1, y2, y3 boundary;
  star-Q4-<r>     a Q4 agent e sharing r goods of degree 2 with r distinct P3 agents.
Reductions searched (all with the unenvied bundle of Lemma M1(b)): DEL; every one-agent gadget h on the boundary goods
plus 0, 1 or 2 gadget goods (at most 4 goods in all), over the menu of valuation classes of k4/reduce4.py; and the copy
gadgets listed per configuration (a twin kept, its partner deleted).

Usage: twins4.py explore CONFIG ... [--jobs=J] [--zs=0,1,2]  coverage only (no certificate)
       twins4.py certify CONFIG ... --write=OUT.json.gz [--zs=...]   greedy certificate (k4/check_twins4.py re-checks)
       twins4.py why CONFIG ... [--show=K]      failing local states for the first K profiles not reduced
       twins4.py list                                       the configuration names
"""
import sys, time, itertools
import numpy as np
import reduce4 as R4


def twins_config(kind, j):
    d = {'Q3': 3, 'Q4': 4}[kind]
    R = tuple(['g%d' % i for i in range(j)] + ['a', 'b', 'c', 'd'][:d - j])
    I = set(R[:j])
    D = set(R[j:])
    return R4.Config('twins-%s-%d' % (kind, j), {'e': R, 'f': R}, I, D)


def twins_p3():
    return R4.Config('twins-P3', {'e': ('G1', 'G2', 'pe'), 'f': ('G1', 'G2', 'pf')}, {'pe', 'pf'}, {'G1', 'G2'})


def near_config(ke, kf, j):
    """e (kind ke) and f (kind kf) share three goods s1, s2, s3; j of them have degree 2 (interior). The remaining goods
    of a 4-good agent are its own boundary good (Q4: 'x'/'y') or private good (P4: 'pe'/'pf'); a 3-good sharer is
    then Q3 with R = {s1, s2, s3}."""
    sh = ['g%d' % i for i in range(j)] + ['s%d' % i for i in range(3 - j)]
    def rest(k, tag):
        return {'Q3': [], 'Q4': ['x' + tag], 'P4': ['p' + tag]}[k]
    Re, Rf = tuple(sh + rest(ke, 'e')), tuple(sh + rest(kf, 'f'))
    I = set(sh[:j]) | {g for g in Re + Rf if g.startswith('p')}
    D = (set(Re) | set(Rf)) - I
    return R4.Config('near-%s-%s-%d' % (ke, kf, j), {'e': Re, 'f': Rf}, I, D)


def dbl_config(ke, kf, shared=0):
    """Double edge: e (kind ke) and f (kind kf), each Q3, P4 or Q4, share two goods g0, g1 that nobody else values;
    their other shared goods are boundary goods, of which `shared` are common to e and f (e's a, b; f's x, y)."""
    def rest(k, tag, names):
        return {'Q3': names[:1], 'P4': names[:1] + ['p' + tag], 'Q4': names[:2]}[k]
    eo = rest(ke, 'e', ['a', 'b'])
    fo = rest(kf, 'f', ['x', 'y'])
    for i in range(shared): fo[i] = eo[i]
    Re, Rf = tuple(['g0', 'g1'] + eo), tuple(['g0', 'g1'] + fo)
    I = {'g0', 'g1'} | {g for g in Re + Rf if g.startswith('p')}
    D = (set(Re) | set(Rf)) - I
    return R4.Config('dbl-%s-%s%s' % (ke, kf, '-c%d' % shared if shared else ''), {'e': Re, 'f': Rf}, I, D)


def xyc_config(ke, kf):
    """Closed single edge: e (ke) and f (kf), each Q3/P4/Q4, share a good g of degree 2 (interior) and a boundary good a;
    their other goods are boundary (e: b, c; f: y, w) or private."""
    def rest(k, tag, names):
        return {'Q3': names[:1], 'P4': names[:1] + ['p' + tag], 'Q4': names[:2]}[k]
    Re = tuple(['g', 'a'] + rest(ke, 'e', ['b', 'c'])); Rf = tuple(['g', 'a'] + rest(kf, 'f', ['y', 'w']))
    I = {'g'} | {x for x in Re + Rf if x.startswith('p')}
    D = (set(Re) | set(Rf)) - I
    return R4.Config('xyc-%s-%s' % (ke, kf), {'e': Re, 'f': Rf}, I, D)


def tri_config(k1, k2, k3):
    """Triangle: agents e1, e2, e3 of kinds Q3/P4/Q4 pairwise sharing a good of degree 2 (g12, g13, g23, interior);
    their other shared goods are boundary goods (e_i's a_i, and b_i for Q4), private goods interior."""
    S, I = {}, {'g12', 'g13', 'g23'}
    for i, k in zip((1, 2, 3), (k1, k2, k3)):
        gs = ['g%d%d' % tuple(sorted((i, j))) for j in (1, 2, 3) if j != i]
        rest = {'Q3': ['a%d' % i], 'P4': ['a%d' % i, 'p%d' % i], 'Q4': ['a%d' % i, 'b%d' % i]}[k]
        S['e%d' % i] = tuple(gs + rest)
        I |= {g for g in rest if g.startswith('p')}
    D = {x for R in S.values() for x in R} - I
    return R4.Config('tri-%s-%s-%s' % (k1, k2, k3), S, I, D)


def claw_config():
    S = {'f%d' % i: ('G', 'y%d' % i, 'p%d' % i) for i in (1, 2, 3)}
    return R4.Config('claw', S, {'G', 'p1', 'p2', 'p3'}, {'y1', 'y2', 'y3'})


def star_config(r):
    """Q4 agent e on g1..gr (degree 2, each shared with a P3 agent fi on gi, yi, pi) and r..3 of its own boundary goods."""
    eg = tuple(['g%d' % i for i in range(1, r + 1)] + ['a', 'b', 'c'][:4 - r])
    S = {'e': eg}
    for i in range(1, r + 1): S['f%d' % i] = ('g%d' % i, 'y%d' % i, 'p%d' % i)
    I = {'g%d' % i for i in range(1, r + 1)} | {'p%d' % i for i in range(1, r + 1)}
    D = {x for R in S.values() for x in R} - I
    return R4.Config('star-Q4-%d' % r, S, I, D)


CONFIGS = {}
for _k, _d in (('Q3', 3), ('Q4', 4)):
    for _j in range(_d):
        CONFIGS['twins-%s-%d' % (_k, _j)] = (lambda k=_k, j=_j: twins_config(k, j))
CONFIGS['twins-P3'] = twins_p3
for _ke, _kf in (('Q3', 'Q3'), ('Q3', 'Q4'), ('Q3', 'P4'), ('Q4', 'Q4'), ('Q4', 'P4'), ('P4', 'P4')):
    for _j in range(4 if 'Q4' in (_ke, _kf) else 3):
        if _ke == _kf == 'Q3': continue                 # that is twins-Q3
        CONFIGS['near-%s-%s-%d' % (_ke, _kf, _j)] = (lambda a=_ke, b=_kf, j=_j: near_config(a, b, j))
_OTHER = {'Q3': 1, 'P4': 1, 'Q4': 2}             # shared goods besides g0, g1
for _ke, _kf in (('Q3', 'Q3'), ('Q3', 'P4'), ('Q3', 'Q4'), ('P4', 'P4'), ('P4', 'Q4'), ('Q4', 'Q4')):
    for _c in range(min(_OTHER[_ke], _OTHER[_kf]) + 1):
        CONFIGS['dbl-%s-%s%s' % (_ke, _kf, '-c%d' % _c if _c else '')] = (lambda a=_ke, b=_kf, c=_c: dbl_config(a, b, c))
for _ke, _kf in (('Q3', 'Q3'), ('Q3', 'P4'), ('P4', 'P4'), ('Q3', 'Q4'), ('P4', 'Q4'), ('Q4', 'Q4')):
    CONFIGS['xyc-%s-%s' % (_ke, _kf)] = (lambda a=_ke, b=_kf: xyc_config(a, b))
for _t in itertools.combinations_with_replacement(('Q3', 'P4', 'Q4'), 3):
    CONFIGS['tri-%s-%s-%s' % _t] = (lambda t=_t: tri_config(*t))
CONFIGS['claw'] = claw_config
for _r in (1, 2, 3, 4):
    CONFIGS['star-Q4-%d' % _r] = (lambda r=_r: star_config(r))


def copy_gadgets(cfg):
    """For two agents e, f: keep one (a copy on the same goods, its interior goods renamed into I'), delete the other."""
    out = []
    if sorted(cfg.S) != ['e', 'f']: return out
    for keep in ('e', 'f'):
        ren = {g: (g + "'" if g in cfg.I else g) for g in cfg.S[keep]}
        Ip = {ren[g] for g in cfg.S[keep] if g in cfg.I}
        out.append(R4.Reduction(cfg, 'KEEP-' + keep, {keep + "'": ('copy', keep, ren)}, Ip, source=True))
    return out


def drop_gadget(cfg):
    """Delete g0 from a double edge: e' and f' copy e and f with g0 and g1 both mapped to one gadget good g' (and
    private goods renamed into I'). Both reduce4.py and check_reductions4.py build a copy's valuation by running
    through the copied agent's goods in order, a later good overwriting an earlier one with the same image, so e' values
    g' at e's value of g1: H' is H with g0 deleted (same agents, one good fewer)."""
    if sorted(cfg.S) != ['e', 'f'] or not {'g0', 'g1'} <= set(cfg.S['e']) & set(cfg.S['f']): return []
    Sp, Ip = {}, {"g'"}
    for s in ('e', 'f'):
        R = cfg.S[s]
        assert R.index('g0') < R.index('g1')
        ren = {g: ("g'" if g in ('g0', 'g1') else g + "'" if g in cfg.priv[s] else g) for g in R}
        Ip |= {ren[g] for g in cfg.priv[s]}
        Sp[s + "'"] = ('copy', s, ren)
    return [R4.Reduction(cfg, 'DROP-g0', Sp, Ip, source=True)]


class BlockReduction(R4.Reduction):
    """A reduction whose extension search keeps each gadget agent's moved items together (they go, as one block, to one
    agent of S or to one free outside bundle). A restriction of reduce4's search: every extension it yields is one that
    reduce4 would also yield (same domination checks), so certificates are checked as usual; it only finds fewer."""

    def extensions(self, Yb, Ob, src):
        cfg = self.cfg
        S = cfg.agents
        Yall = list(Yb.values()) + Ob
        Ysrc = None if src is None else (Yb[src[1]] if src[0] == 'sp' else Ob[src[1]])
        blocks_mv = [[x for x in Yb[s] if x not in self.Ip] for s in sorted(Yb)]
        blocks_mv = [b for b in blocks_mv if b]
        ipblocks = [k for k, b in enumerate(Ob) if any(x in self.Ip for x in b) or src == ('O', k)]
        Ibase = [[x for x in b if x not in self.Ip] for b in Ob]
        free = [k for k in ipblocks if not self.U(Ob[k]) and any(x in self.Ip for x in Ob[k])]
        dest = S + [('O', k) for k in free]
        Ig = sorted(cfg.I)
        choices = [S + [('O', k) for k in ipblocks] for g in Ig]
        Udom = [self.U(B) for B in Yall] + ([self.U(Ysrc)] if Ysrc is not None else [])
        for mv in itertools.product(dest, repeat=len(blocks_mv)):
            Xs0 = {s: [] for s in S}
            Ib0 = [list(b) for b in Ibase]
            for blk, d in zip(blocks_mv, mv):
                (Ib0[d[1]] if isinstance(d, tuple) else Xs0[d]).extend(blk)
            if any(len(self.U(B)) >= 2 and not any(self.U(B) <= u for u in Udom) for B in list(Xs0.values()) + Ib0):
                continue
            for ch in itertools.product(*choices):
                Xs = {s: list(Xs0[s]) for s in S}
                Ox = [list(b) for b in Ib0]
                for g, c in zip(Ig, ch):
                    (Ox[c[1]] if isinstance(c, tuple) else Xs[c]).append(g)
                if not all(self.dominated(Xs[s], Yall, Ysrc) for s in S): continue
                if not all(self.dominated(Ox[k], Yall, Ysrc) for k in ipblocks): continue
                yield Xs, Ox


def gadget_menu(cfg, nz, jobs):
    """One-agent gadgets h on T + nz gadget goods, T = D (or every subset of D of size 4 - nz when |D| + nz > 4), every
    class of the menu: list of (ok array menu x profiles, goods, menu)."""
    D = sorted(cfg.D)
    out = []
    Ts = [D] if len(D) + nz <= 4 else [list(T) for T in itertools.combinations(D, 4 - nz)]
    for T in Ts:
        goods = list(T) + ["z%d'" % i for i in range(nz)]
        if not goods or (nz and len(D) + nz > 4 and not T): continue
        Ip = set(goods) - set(D)
        M = R4.menu(len(goods))
        out.append((R4.gadget_search(cfg, 'h', goods, Ip, M, jobs), goods, M))
    return out


def explore(cfg, jobs=4, zs=(0, 1, 2), verbose=True, copies=False):
    total = int(np.prod(cfg.shape))
    print('configuration %s: agents %s, I = %s, D = %s, %d profiles' % (cfg.name, cfg.S, sorted(cfg.I), sorted(cfg.D),
                                                                       total), flush=True)
    union = np.zeros(cfg.shape, dtype=bool)
    for red in [R4.Reduction(cfg, 'DEL', {}, set(), source=True)] + (copy_gadgets(cfg) if copies else []) + \
            (drop_gadget(cfg) if '--drop' in sys.argv else []):
        t = time.time()
        ok, _ = R4.run(red, jobs)
        union |= ok
        print('  %-8s reduces %7d of %d (%.1f s)' % (red.name, ok.sum(), total, time.time() - t), flush=True)
    for nz in zs:
        for ok, goods, M in gadget_menu(cfg, nz, jobs):
            u = ok.any(0).reshape(cfg.shape)
            print('  gadget h on %s (%d menu valuations): %d of %d reduced, new %d' % (
                goods, len(M), u.sum(), total, (u & ~union).sum()), flush=True)
            if verbose and u.any():
                need, chosen = u.ravel().copy(), []
                while need.any():
                    k = int((ok & need).sum(1).argmax()); chosen.append(k); need &= ~ok[k]
                for k in chosen[:6]: print('    h = %s reduces %d' % (dict(zip(goods, M[k].tolist())), ok[k].sum()))
                if len(chosen) > 6: print('    ... %d gadgets in a greedy cover' % len(chosen))
            union |= u
    print('  together: %d of %d profiles' % (union.sum(), total), flush=True)
    return union


def certify(cfg, jobs=4, zs=(0, 1, 2), copies=False):
    """Greedy certificate for cfg: DEL (and the copy gadgets if `copies`) plus every one-agent gadget of the menus; each
    chosen menu gadget is re-run directly (its coverage must agree with the menu search). Returns (union, records)."""
    cands = []
    for red in [R4.Reduction(cfg, 'DEL', {}, set(), source=True)] + (copy_gadgets(cfg) if copies else []):
        ok, kept = R4.run(red, jobs)
        cands.append((ok, red, kept))
    for nz in zs:
        for okm, goods, M in gadget_menu(cfg, nz, jobs):
            Ip = set(goods) - set(cfg.D)
            for k in np.nonzero(okm.any(1))[0]:
                name = 'GAD-h(' + ','.join('%s=%d' % (g, v) for g, v in zip(goods, M[k])) + ')'
                red = R4.Reduction(cfg, name, {'h': ('fix', {g: int(v) for g, v in zip(goods, M[k])})}, Ip, source=True)
                cands.append((okm[k].reshape(cfg.shape), red, None))
    union = np.zeros(cfg.shape, dtype=bool)
    for ok, _, _ in cands: union |= ok
    need, recs = union.copy(), []
    while need.any():
        ok, red, kept = max(cands, key=lambda c: int((c[0] & need).sum()))
        if kept is None:
            ok2, kept = R4.run(red, jobs)
            assert (ok2 == ok).all(), 'gadget search and direct run disagree: %s' % red.name
        recs.append(R4.record(red, R4.select(cfg, kept, ok), int(ok.sum())))
        print('    %-44s reduces %6d, new %6d' % (red.name, ok.sum(), (ok & need).sum()), flush=True)
        need &= ~ok
    return union, recs


def failing_state(red, prof):
    """An admissible local state of Y (for profile prof) with no extension under which every agent of S is safe."""
    cfg = red.cfg
    for Yb, Ob, src in red.states():
        adm = R4.adm_array(cfg, red.admissible(Yb, Ob, src))
        if adm is None or not adm[prof]: continue
        if not any(all(R4.safe_mask(cfg, s, v)[k] for s, v, k in zip(cfg.agents, R4.views_of(cfg, *X), prof))
                   for X in red.extensions(Yb, Ob, src)):
            return Yb, Ob, src
    return None


def why(cfg, jobs=4, zs=(0, 1, 2), nshow=1):
    """For the first unreduced profiles: the failing state of DEL and of the menu gadget closest to reducing it."""
    u = explore(cfg, jobs, zs, verbose=False)
    left = list(zip(*np.nonzero(~u)))
    print('  %d profiles not reduced' % len(left))
    menus = [m for nz in zs for m in gadget_menu(cfg, nz, jobs)]
    for prof in left[:nshow]:
        print('  profile', {s: cfg.valuation(s, k) for s, k in zip(cfg.agents, prof)})
        reds = [R4.Reduction(cfg, 'DEL', {}, set(), source=True)]
        for ok, goods, M in menus[:1]:
            k = int(ok.sum(1).argmax())
            reds.append(R4.Reduction(cfg, 'GAD-h%s' % dict(zip(goods, M[k].tolist())),
                                     {'h': ('fix', {g: int(v) for g, v in zip(goods, M[k])})}, set(goods) - cfg.D,
                                     source=True))
        for red in reds:
            st = failing_state(red, prof)
            print('    %s: %s' % (red.name, 'no failing state' if st is None else
                                  "Y: S' %s | outside %s | unenvied %s" % st))
    return left


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    opts = dict(a[2:].split('=', 1) for a in sys.argv[1:] if a.startswith('--') and '=' in a)
    jobs = int(opts.get('jobs', 4))
    zs = tuple(int(x) for x in opts.get('zs', '0,1,2').split(','))
    if args[0] == 'list':
        for k in CONFIGS: print(k)
        return
    if args[0] == 'certify':
        import gzip, json
        recs = []
        for name in args[1:]:
            cfg = CONFIGS[name]()
            total = int(np.prod(cfg.shape))
            print('configuration %s: agents %s, I = %s, D = %s, %d profiles' % (cfg.name, cfg.S, sorted(cfg.I),
                                                                               sorted(cfg.D), total), flush=True)
            union, r = certify(cfg, jobs, zs)
            print('  reduced: %d of %d profiles (%d records)' % (union.sum(), total, len(r)), flush=True)
            recs += r
        with gzip.open(opts['write'], 'wt') as f: json.dump(recs, f)
        print('wrote %s: %d records, %d states' % (opts['write'], len(recs), sum(len(r['states']) for r in recs)))
        return
    if args[0] == 'why':
        for name in args[1:]: why(CONFIGS[name](), jobs, zs, int(opts.get('show', 1)))
        return
    if args[0] == 'explore':
        for name in args[1:]:
            cfg = CONFIGS[name]()
            u = explore(cfg, jobs, zs, copies='--copies' in sys.argv)
            left = list(zip(*np.nonzero(~u)))
            if 0 < len(left) <= 12:
                for prof in left: print('    not reduced:', {s: cfg.valuation(s, k) for s, k in zip(cfg.agents, prof)})


if __name__ == '__main__':
    main()
