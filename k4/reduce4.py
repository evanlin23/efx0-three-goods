"""k = 4 local reductions for a minimal counterexample to TARGET4 (k4/MINCEX.md, Lemma K4.M1).

The k = 3 checker src/reduce.py decides one ranking profile at a time. At k = 4 an agent with 4 goods has one of 288
strict balanced order types (k4/order_types.json; 144 when it has two private goods p, q, which must satisfy
p + q < s + t in a core), so this version decides a reduction for *all* type profiles of the configuration at once:

  configuration: agents S (3 or 4 goods each), interior goods I (valued by no agent outside S), boundary goods D;
  reduction: gadget agents S' (each either a fixed additive valuation, or a copy of an agent s of S with its goods
  renamed, so that its valuation depends on s's type) and gadget goods I'; option 'source' = Lemma M1(b).

For every local state of an allocation Y of H' (as in src/reduce.py: each good of I' + D held by an agent of S' or
lying in an outside bundle, which goods share an outside bundle, whether each bundle also holds goods outside the
configuration, and with 'source' which bundle is unenvied), the admissible profiles are those under which every agent
of S' is safe (and envies no unenvied bundle); every extension X allowed by Lemma M1 (moved items and interior goods
placed, every new or modified bundle dominated) covers the profiles under which every agent of S is safe in X. A
profile is reduced when every state admissible for it has an extension covering it. Safety is the raw EFX0
definition evaluated with each type's integer representative; an agent's safety depends only on its type, so one
representative per type decides it.

Goods are strings. 'w:<s'>' stands for the goods outside the configuration held by gadget agent s'; 'W:<k>' for those
in outside bundle k. The certificate (see certificate()) lists, per admissible state, a few extensions whose union
covers the reduced profiles; k4/check_reductions4.py re-derives everything else.
"""
import itertools, json, os, sys, gzip
import numpy as np
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
_OT = json.load(open(os.path.join(HERE, 'order_types.json')))
TYPES = {d: [tuple(t['rep']) for t in _OT[str(d)]['types'] if t['strict'] and t['balanced']] for d in (3, 4)}
assert len(TYPES[3]) == 6 and len(TYPES[4]) == 288


def is_marker(x):
    return x.startswith('w:') or x.startswith('W:')


class Config:
    """S: {agent: tuple of goods}; I: interior goods; D: boundary goods. An interior good valued by exactly one agent of
    S is private to it (no agent of H values it), so its type domain is restricted as in a k = 4 core."""

    def __init__(self, name, S, I, D):
        self.name, self.S, self.I, self.D = name, {s: tuple(R) for s, R in S.items()}, set(I), set(D)
        self.agents = sorted(self.S)
        assert not self.I & self.D
        for s, R in self.S.items():
            assert len(set(R)) == len(R) in (3, 4) and set(R) <= self.I | self.D, (s, R)
        self.priv = {s: [g for g in R if g in self.I and sum(g in R2 for R2 in self.S.values()) == 1]
                     for s, R in self.S.items()}
        self.dom = {}                                   # agent -> list of value vectors aligned with S[s]
        for s, R in self.S.items():
            P = self.priv[s]
            assert len(P) <= len(R) - 2, 'not a core agent: %s' % s
            doms = []
            for t in TYPES[len(R)]:
                val = dict(zip(R, t))
                if len(R) == 4 and len(P) == 2:
                    if sum(val[g] for g in P) >= sum(val[g] for g in R if g not in P): continue
                doms.append(t)
            self.dom[s] = doms
        self.shape = tuple(len(self.dom[s]) for s in self.agents)
        self.V = {s: np.array(self.dom[s], dtype=np.int64) for s in self.agents}    # types x goods

    def valuation(self, s, k):
        return dict(zip(self.S[s], self.dom[s][k]))


class Reduction:
    """Sp: {gadget agent: ('fix', {good: value}) or ('copy', s, {good of S[s]: good of I' + D})}; Ip: gadget goods."""

    def __init__(self, cfg, name, Sp, Ip, source=False):
        self.cfg, self.name, self.Sp, self.Ip, self.source = cfg, name, dict(Sp), set(Ip), source
        assert not self.Ip & cfg.D and not self.Ip & cfg.I
        for sp, spec in self.Sp.items():
            goods = set(spec[1]) if spec[0] == 'fix' else set(spec[2].values())
            assert goods <= self.Ip | cfg.D and len(goods) <= 4, (sp, spec)
        self.L = sorted(self.Ip | cfg.D)
        self.sps = sorted(self.Sp)

    # ----- valuations of gadget agents: list of (dependency agent or None, list of value dicts) -----
    def sp_vals(self, sp):
        spec = self.Sp[sp]
        if spec[0] == 'fix': return None, [dict(spec[1])]
        s, ren = spec[1], spec[2]
        return s, [{ren[g]: v for g, v in zip(self.cfg.S[s], t)} for t in self.cfg.dom[s]]

    # ----- local states of Y -----
    def states(self):
        L, sps = self.L, self.sps

        def rec(k, spb, blocks):
            if k == len(L):
                yield {s: list(b) for s, b in spb.items()}, [list(b) for b in blocks]
                return
            g = L[k]
            for s in sps:
                spb[s].append(g); yield from rec(k + 1, spb, blocks); spb[s].pop()
            for b in blocks:
                b.append(g); yield from rec(k + 1, spb, blocks); b.pop()
            blocks.append([g]); yield from rec(k + 1, spb, blocks); blocks.pop()

        for spb, blocks in rec(0, {s: [] for s in sps}, []):
            for wf in itertools.product((0, 1), repeat=len(sps)):
                for Wf in itertools.product((0, 1), repeat=len(blocks)):
                    Yb = {s: spb[s] + (['w:' + s] if wf[i] else []) for i, s in enumerate(sps)}
                    Ob = [blocks[k] + (['W:%d' % k] if Wf[k] else []) for k in range(len(blocks))]
                    if not self.source:
                        yield Yb, Ob, None; continue
                    for s in sps: yield Yb, Ob, ('sp', s)
                    for k in range(len(Ob)): yield Yb, Ob, ('O', k)
                    k = len(Ob)
                    yield Yb, Ob + [[]], ('O', k)
                    yield Yb, Ob + [['W:%d' % k]], ('O', k)

    def admissible(self, Yb, Ob, src):
        """Per gadget agent: (dependency agent, boolean array over its types) or (None, bool)."""
        out = []
        Bsrc = None if src is None else (Yb[src[1]] if src[0] == 'sp' else Ob[src[1]])
        for sp in self.sps:
            dep, vals = self.sp_vals(sp)
            others = [B for t, B in Yb.items() if t != sp] + Ob
            ok = []
            for val in vals:
                own = sum(val.get(g, 0) for g in Yb[sp])
                good = all(theta(val, B) <= own for B in others)
                if good and Bsrc is not None and sum(val.get(g, 0) for g in Bsrc) > own: good = False
                ok.append(good)
            out.append((dep, np.array(ok)) if dep is not None else (None, ok[0]))
        return out

    # ----- domination (Lemma M1) -----
    def U(self, B):
        return frozenset(x for x in B if x in self.cfg.D or is_marker(x))

    def inner(self, B):
        return any(x in self.cfg.I or x in self.Ip for x in B)

    def dominated(self, B, Yall, Ysrc):
        # |B| <= 1: a singleton is never a threat. The one-token bundle {'w:s''} stands for all the outside goods s'
        # held in Y (moved as a whole); it is safe to call it dominated, because it is dominated by Y_{s'} itself.
        if len(B) <= 1: return True
        u = self.U(B)
        if not u: return True
        if Ysrc is not None and u <= self.U(Ysrc): return True
        inn = self.inner(B)
        return any(u <= self.U(B2) and (not inn or self.inner(B2) or u != self.U(B2)) for B2 in Yall)

    # ----- extensions -----
    def extensions(self, Yb, Ob, src):
        """Yield every extension X = (S-bundles, outside bundles) allowed by Lemma M1 (M1(b) with 'source')."""
        cfg = self.cfg
        S = cfg.agents
        Yall = list(Yb.values()) + Ob
        Ysrc = None if src is None else (Yb[src[1]] if src[0] == 'sp' else Ob[src[1]])
        moved = [x for s in sorted(Yb) for x in Yb[s] if x not in self.Ip]
        ipblocks = [k for k, b in enumerate(Ob) if any(x in self.Ip for x in b) or src == ('O', k)]
        Ibase = [[x for x in b if x not in self.Ip] for b in Ob]
        free = [k for k in ipblocks if not self.U(Ob[k]) and any(x in self.Ip for x in Ob[k])]
        dest = S + [('O', k) for k in free]
        Ig = sorted(cfg.I)
        choices = [S + [('O', k) for k in ipblocks] for g in Ig]
        Udom = [self.U(B) for B in Yall] + ([self.U(Ysrc)] if Ysrc is not None else [])
        for mv in itertools.product(dest, repeat=len(moved)):
            Xs0 = {s: [] for s in S}
            Ib0 = [list(b) for b in Ibase]
            for x, d in zip(moved, mv):
                (Ib0[d[1]] if isinstance(d, tuple) else Xs0[d]).append(x)
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


def theta(val, B):
    if len(B) <= 1: return 0
    vs = [val.get(g, 0) for g in B]
    return sum(vs) - min(vs)


def view(R, own, others):
    """What agent with goods R sees of an allocation: its own part, and each other bundle's part in R with a flag
    'contains a good outside R' (bundles of <= 1 good and bundles missing R are never threats)."""
    Rs = set(R)
    thr = set()
    for B in others:
        T = frozenset(g for g in B if g in Rs)
        if len(B) >= 2 and T: thr.add((T, len(T) < len(B)))
    return frozenset(g for g in own if g in Rs), frozenset(thr)


_MASK = {}


def safe_mask(cfg, s, vw):
    """Boolean array over s's types: safe under this view (raw EFX0 definition with the integer representatives)."""
    key = (cfg.name, s, vw)
    if key in _MASK: return _MASK[key]
    R, V = cfg.S[s], cfg.V[s]
    idx = {g: i for i, g in enumerate(R)}
    own, thr = vw
    mine = V[:, [idx[g] for g in own]].sum(1) if own else np.zeros(len(V), dtype=np.int64)
    ok = np.ones(len(V), dtype=bool)
    for T, extra in thr:
        cols = V[:, [idx[g] for g in T]]
        t = cols.sum(1) if extra else cols.sum(1) - cols.min(1)
        ok &= mine >= t
    _MASK[key] = ok
    return ok


def views_of(cfg, Xs, Ox):
    out = []
    for s in cfg.agents:
        others = [B for t, B in Xs.items() if t != s] + Ox
        out.append(view(cfg.S[s], Xs[s], others))
    return tuple(out)


def outer(masks):
    arr = masks[0]
    for m in masks[1:]: arr = np.logical_and.outer(arr, m)
    return arr


def adm_array(cfg, adm):
    arr = np.ones(cfg.shape, dtype=bool)
    for dep, m in adm:
        if dep is None:
            if not m: return None
        else:
            ax = cfg.agents.index(dep)
            sh = [1] * len(cfg.shape); sh[ax] = len(m)
            arr = arr & m.reshape(sh)
    return arr if arr.any() else None


# ----- one state: its admissible profiles and its candidate extensions (one per distinct pair of views) -----
_RED = None


def _init(red):
    global _RED
    _RED = red


def _state(st):
    """Admissible types of the state and its non-dominated extensions: [(safe masks per agent of S, X)]."""
    Yb, Ob, src = st
    red = _RED
    cfg = red.cfg
    adm = red.admissible(Yb, Ob, src)
    if adm_array(cfg, adm) is None: return None
    seen, items = set(), []
    for Xs, Ox in red.extensions(Yb, Ob, src):
        vw = views_of(cfg, Xs, Ox)
        if vw in seen: continue
        seen.add(vw)
        masks = [safe_mask(cfg, s, v) for s, v in zip(cfg.agents, vw)]
        if all(m.any() for m in masks): items.append((masks, (Xs, Ox)))
    items.sort(key=lambda it: -int(np.prod([m.sum() for m in it[0]])))
    keep = []
    for masks, X in items:
        if not any(all((m & ~k).sum() == 0 for m, k in zip(masks, km)) for km, _ in keep): keep.append((masks, X))
    return st, adm, keep


def run(red, jobs=4):
    """Return (reduced-profile array, list of (state, admissible array, [(masks, X)])) for the reduction."""
    cfg = red.cfg
    sts = list(red.states())
    if jobs > 1:
        with Pool(jobs, initializer=_init, initargs=(red,)) as pool:
            res = pool.map(_state, sts, chunksize=max(1, len(sts) // (8 * jobs)))
    else:
        _init(red); res = [_state(st) for st in sts]
    bad = np.zeros(cfg.shape, dtype=bool)
    kept = []
    for r in res:
        if r is None: continue
        st, adm, items = r
        A = adm_array(cfg, adm)
        cov = np.zeros(cfg.shape, dtype=bool)
        for masks, _ in items: cov |= outer(masks)
        bad |= A & ~cov
        kept.append((st, A, items))
    return ~bad, kept


def select(cfg, kept, target):
    """Per admissible state, a greedy set of extensions covering (admissible & target)."""
    out = []
    for st, A, items in kept:
        need = A & target
        if not need.any(): continue
        chosen = []
        while need.any():
            best, bc = None, 0
            for masks, X in items:
                c = int((outer(masks) & need).sum())
                if c > bc: best, bc = (masks, X), c
            assert best is not None, 'uncovered state'
            chosen.append(best[1]); need &= ~outer(best[0])
        out.append((st, chosen))
    return out


# ----- certificates -----
def canon(Yb, Ob, src):
    """Canonical key of a state and the renaming of its outside-bundle markers (blocks sorted with the marker read as
    'W'; marker of the block at sorted position i becomes 'W:i')."""
    tag = sorted((tuple(sorted('W' if x.startswith('W:') else x for x in b)), k) for k, b in enumerate(Ob))
    pos = {k: i for i, (_, k) in enumerate(tag)}
    ren = {'W:%d' % k: 'W:%d' % pos[k] for k in range(len(Ob))}
    blocks = [None] * len(Ob)
    for k, b in enumerate(Ob): blocks[pos[k]] = sorted(ren.get(x, x) for x in b)
    sd = None if src is None else (['sp', src[1]] if src[0] == 'sp' else ['O', pos[src[1]]])
    key = json.dumps([[sorted(Yb[s]) for s in sorted(Yb)], blocks, sd])
    return key, pos, ren


def export_X(X, pos, ren):
    Xs, Ox = X
    O = [None] * len(Ox)
    for k, b in enumerate(Ox): O[pos[k]] = sorted(ren.get(x, x) for x in b)
    return {'S': {s: sorted(ren.get(x, x) for x in B) for s, B in Xs.items()}, 'O': O}


def record(red, sel, n_reduced):
    cfg = red.cfg
    st = []
    for (Yb, Ob, src), Xl in sel:
        key, pos, ren = canon(Yb, Ob, src)
        st.append([key, [export_X(X, pos, ren) for X in Xl]])
    return {'config': cfg.name, 'name': red.name, 'S': {s: list(R) for s, R in cfg.S.items()},
            'I': sorted(cfg.I), 'D': sorted(cfg.D),
            'Sp': {sp: ({'fix': spec[1]} if spec[0] == 'fix' else {'copy': spec[1], 'map': spec[2]})
                   for sp, spec in red.Sp.items()},
            'Ip': sorted(red.Ip), 'source': red.source, 'reduced': n_reduced, 'states': st}


# ----- gadget search: one reduction structure, a menu of fixed valuations for its gadget agents -----
def _cover(st):
    """Coverage array of a state (profiles some extension covers), and its non-dominated extensions."""
    Yb, Ob, src = st
    red = _RED
    cfg = red.cfg
    seen, items = set(), []
    for Xs, Ox in red.extensions(Yb, Ob, src):
        vw = views_of(cfg, Xs, Ox)
        if vw in seen: continue
        seen.add(vw)
        masks = [safe_mask(cfg, s, v) for s, v in zip(cfg.agents, vw)]
        if all(m.any() for m in masks): items.append((masks, (Xs, Ox)))
    cov = np.zeros(cfg.shape, dtype=bool)
    for masks, _ in items: cov |= outer(masks)
    return np.packbits(cov.ravel())


def menu_admissible(goods, M, Yb, Ob, src, sp):
    """Boolean vector over the menu rows M (valuations of gadget agent sp on `goods`): sp safe in the state (and, with
    an unenvied bundle, not envying it)."""
    idx = {g: i for i, g in enumerate(goods)}
    def val(B):
        cols = [idx[g] for g in B if g in idx]
        return M[:, cols].sum(1) if cols else np.zeros(len(M), dtype=np.int64)
    own = val(Yb[sp])
    ok = np.ones(len(M), dtype=bool)
    for t, B in list(Yb.items()) + [(None, B) for B in Ob]:
        if t == sp or len(B) <= 1: continue
        cols = [idx[g] for g in B if g in idx]
        if not cols: continue
        V = M[:, cols]
        if len(cols) < len(B): thr = V.sum(1)
        else: thr = V.sum(1) - V.min(1)
        ok &= own >= thr
    if src is not None:
        Bs = Yb[src[1]] if src[0] == 'sp' else Ob[src[1]]
        ok &= val(Bs) <= own
    return ok


def gadget_search(cfg, sp, goods, Ip, M, jobs=4):
    """One gadget agent sp valuing `goods` (subset of I' + D) with each valuation of the menu M (rows); returns a boolean
    array (menu x profiles): the menu item reduces the profile (Lemma M1(b))."""
    red = Reduction(cfg, 'search', {sp: ('fix', dict(zip(goods, M[0])))}, Ip, source=True)
    sts = list(red.states())
    if jobs > 1:
        with Pool(jobs, initializer=_init, initargs=(red,)) as pool:
            covs = pool.map(_cover, sts, chunksize=max(1, len(sts) // (8 * jobs)))
    else:
        _init(red); covs = [_cover(st) for st in sts]
    P = int(np.prod(cfg.shape))
    notcov = np.array([~np.unpackbits(c)[:P].astype(bool) for c in covs], dtype=np.float32)   # states x profiles
    adm = np.array([menu_admissible(goods, M, *st, sp) for st in sts], dtype=np.float32)       # states x menu
    bad = adm.T @ notcov > 0.5
    return ~bad


def menu(k, top=10):
    """One valuation per behavior class (signs of v(S) - v(T) over disjoint S, T, and which goods are positive) of k
    goods, with values in 0..top."""
    subs = [(S, T) for S in range(1, 1 << k) for T in range(1, 1 << k) if not S & T]
    vecs = np.array(list(itertools.product(range(top + 1), repeat=k)), dtype=np.int64)
    vecs = vecs[vecs.sum(1) > 0]
    bits = np.array([[S >> i & 1 for i in range(k)] for S in range(1 << k)], dtype=np.int64)
    sums = vecs @ bits.T
    sig = np.stack([np.sign(sums[:, S] - sums[:, T]) for S, T in subs] + [(vecs > 0).astype(np.int64).T[i]
                                                                           for i in range(k)], axis=1)
    _, first = np.unique(sig, axis=0, return_index=True)
    return vecs[np.sort(first)]
