"""Local reducibility checker for a minimal counterexample (proofs/min_counterexample.md, Lemma M1).

A configuration is a set S of agents (each with a strict ranking a > b > c of its three goods), its interior goods I
(valued by no agent outside S) and its boundary goods D (valued by an agent of S and by unknown outside agents). A
reduction replaces (S, I) by a gadget (S', I'): agents S' with explicit additive valuations on I' + D. The checker
enumerates every local state of an allocation Y of the reduced instance (where each good of I' + D is: held by an agent
of S', or in an outside bundle; which goods share an outside bundle; whether each bundle also holds goods outside the
configuration), keeps the states in which every agent of S' is safe, and for each one searches for an extension X in
which every agent of S is safe and every new or modified bundle is dominated by a bundle of Y (Lemma M1). Safety of the
agents of S is computed from the raw EFX0 definition under two balanced realizations of each ranking, which must agree.

Goods are strings. Markers stand for goods outside the configuration: 'w:<s'>' for those held by agent s' of S', and
'W:<k>' for those in outside bundle k. They are worthless to agents of S and S' and valued by outside agents.
"""
import itertools, sys, json, collections

REALS = [(4.0, 3.0, 2.0), (10.0, 9.0, 2.0)]        # balanced realizations of a > b > c


def theta(val, B):
    if len(B) <= 1: return 0.0
    vs = [val.get(g, 0.0) for g in B]
    return sum(vs) - min(vs)


def safe(val, own, others):
    v = sum(val.get(g, 0.0) for g in own)
    return all(theta(val, B) <= v + 1e-9 for B in others)


def realize(rank, r):
    return dict(zip(rank, r))


class Reduction:
    """S: {agent: (a, b, c)}; I, D: sets of goods; Sp: {agent: {good: value}} (or a ranking tuple, realized as
    (4, 3, 2)); Ip: set of gadget goods; Ddel: boundary goods absent from H' (placed by the extension; the domination
    condition forces them to be alone)."""

    def __init__(self, S, I, D, Sp, Ip, name='', Ddel=()):
        self.S, self.I, self.D, self.Ip, self.name = dict(S), set(I), set(D), set(Ip), name
        self.Ddel = set(Ddel)                          # boundary goods deleted from H' (they must end up alone in X)
        assert self.Ddel <= self.D
        self.Sp = {s: (v if isinstance(v, dict) else realize(v, REALS[0])) for s, v in Sp.items()}
        for s, R in self.S.items():
            assert len(set(R)) == 3 and set(R) <= self.I | self.D, (s, R)
        for s, v in self.Sp.items():
            assert set(g for g, x in v.items() if x > 0) <= self.Ip | self.D, (s, v)
        assert not (self.I & self.D) and not (self.Ip & self.D)
        used = set(g for R in self.S.values() for g in R)
        assert self.D <= used, "every boundary good must be valued by an agent of S"
        self.L = sorted(self.Ip | (self.D - self.Ddel))

    # ----- local states of Y -----
    def y_states(self):
        sp = sorted(self.Sp)
        L = self.L
        assign = {}

        def rec(k, spb, blocks):
            if k == len(L):
                yield {s: list(b) for s, b in spb.items()}, [list(b) for b in blocks]
                return
            g = L[k]
            for s in sp:
                spb[s].append(g); yield from rec(k + 1, spb, blocks); spb[s].pop()
            for b in blocks:
                b.append(g); yield from rec(k + 1, spb, blocks); b.pop()
            blocks.append([g]); yield from rec(k + 1, spb, blocks); blocks.pop()

        for spb, blocks in rec(0, {s: [] for s in sp}, []):
            for wf in itertools.product((0, 1), repeat=len(sp)):
                for Wf in itertools.product((0, 1), repeat=len(blocks)):
                    Yb = {s: spb[s] + (['w:' + s] if wf[i] else []) for i, s in enumerate(sp)}
                    Ob = [blocks[k] + (['W:%d' % k] if Wf[k] else []) for k in range(len(blocks))]
                    yield Yb, Ob

    def sp_safe(self, Yb, Ob):
        bundles = list(Yb.values()) + Ob
        for s, val in self.Sp.items():
            others = [B for t, B in Yb.items() if t != s] + Ob
            if not safe(val, Yb[s], others): return False
        return True

    # ----- domination (Lemma M1) -----
    def U(self, B):
        return frozenset(x for x in B if x in self.D or x.startswith('w:') or x.startswith('W:'))

    def inner(self, B):
        return any(x in self.I or x in self.Ip for x in B)

    def dominated(self, B, Yall):
        if len(B) <= 1: return True
        u = self.U(B)
        if not u: return True
        inn = self.inner(B)
        for B2 in Yall:
            u2 = self.U(B2)
            if u <= u2 and (not inn or self.inner(B2) or u != u2): return True
        return False

    # ----- extensions -----
    def s_safe_all(self, Xs, Ox):
        for s, R in self.S.items():
            others = [B for t, B in Xs.items() if t != s] + Ox
            res = {safe(realize(R, r), Xs[s], others) for r in REALS}
            if len(res) != 1: raise SystemExit('realizations disagree for %s' % s)
            if not res.pop(): return False
        return True

    def extend(self, Yb, Ob):
        """Search an extension X; return (S-bundles, outside bundles) or None."""
        S = sorted(self.S)
        Yall = list(Yb.values()) + Ob
        # items from S'-bundles that must move to S-bundles: boundary goods and w-markers
        moved = [x for s in sorted(Yb) for x in Yb[s] if x not in self.Ip] + sorted(self.Ddel)
        ipblocks = [k for k, b in enumerate(Ob) if any(x in self.Ip for x in b)]
        Ibase = [[x for x in b if x not in self.Ip] for b in Ob]
        Igoods = sorted(self.I)
        # preferred order for interior goods: an owner first (agents of S valuing it), then the others
        owners = {g: [s for s in S if g in self.S[s]] for g in Igoods}
        choicesI = {g: owners[g] + [s for s in S if s not in owners[g]] + [('O', k) for k in ipblocks] for g in Igoods}
        # outside bundles made only of gadget goods (worth 0 to their owner) may also receive moved items
        free = [k for k in ipblocks if not self.U(Ob[k])]
        dest = S + [('O', k) for k in free]
        for mv in itertools.product(dest, repeat=len(moved)):
            Xs0 = {s: [] for s in S}
            Ib0 = [list(b) for b in Ibase]
            for x, s in zip(moved, mv):
                if isinstance(s, tuple): Ib0[s[1]].append(x)
                else: Xs0[s].append(x)
            # prune: U-part of each S-bundle is final; it must be dominated unless the bundle stays a singleton
            ok = True
            for B in list(Xs0.values()) + Ib0:
                u = self.U(B)
                if len(u) >= 2 and not any(u <= self.U(B2) for B2 in Yall): ok = False; break
            if not ok: continue
            for ch in itertools.product(*(choicesI[g] for g in Igoods)):
                Xs = {s: list(Xs0[s]) for s in S}
                Ox = [list(b) for b in Ib0]
                for g, c in zip(Igoods, ch):
                    if isinstance(c, tuple): Ox[c[1]].append(g)
                    else: Xs[c].append(g)
                if not all(self.dominated(Xs[s], Yall) for s in S): continue
                if not all(self.dominated(Ox[k], Yall) for k in ipblocks): continue
                if self.s_safe_all(Xs, Ox): return Xs, Ox
        return None

    def check(self, stop_at_first=True, verbose=False):
        """Return (number of admissible local states, list of failing states)."""
        n_adm, fails = 0, []
        for Yb, Ob in self.y_states():
            if not self.sp_safe(Yb, Ob): continue
            n_adm += 1
            if self.extend(Yb, Ob) is None:
                fails.append((Yb, Ob))
                if stop_at_first: break
        return n_adm, fails


def fmt_state(Yb, Ob):
    return 'S\': ' + ', '.join('%s=%s' % (s, '{' + ','.join(b) + '}') for s, b in sorted(Yb.items())) + \
        ' | outside: ' + ', '.join('{' + ','.join(b) + '}' for b in Ob)


# ----- certificates (re-checked independently by tools/check_reductions.py) -----
def canon_state(Yb, Ob):
    """Canonical key of a local state and the renaming of its outside-bundle markers: blocks are sorted (a block's
    marker counted as 'W'), then marker 'W:k' is renamed after its block's position in that order."""
    tagged = sorted((tuple(sorted('W' if x.startswith('W:') else x for x in b)), k) for k, b in enumerate(Ob))
    pos = {k: i for i, (_, k) in enumerate(tagged)}
    ren = {'W:%d' % k: 'W:%d' % pos[k] for k in range(len(Ob))}
    blocks = [None] * len(Ob)
    for k, b in enumerate(Ob): blocks[pos[k]] = sorted(ren.get(x, x) for x in b)
    key = json.dumps([[sorted(Yb[s]) for s in sorted(Yb)], [list(b) for b in sorted(tuple(b) for b in blocks)]])
    return key, pos, ren


def export_ext(Ob, ext, pos, ren):
    Xs, Ox = ext
    O = [None] * len(Ox)
    for k, b in enumerate(Ox): O[pos[k]] = sorted(ren.get(x, x) for x in b)
    return {'S': {s: sorted(ren.get(x, x) for x in B) for s, B in Xs.items()}, 'O': O}


def certificate(red):
    """Record for tools/check_reductions.py, or None if some admissible state has no extension."""
    st = []
    for Yb, Ob in red.y_states():
        if not red.sp_safe(Yb, Ob): continue
        ext = red.extend(Yb, Ob)
        if ext is None: return None
        key, pos, ren = canon_state(Yb, Ob)
        st.append([key, export_ext(Ob, ext, pos, ren)])
    return {'name': red.name, 'S': {s: list(R) for s, R in red.S.items()}, 'I': sorted(red.I), 'D': sorted(red.D),
            'Ddel': sorted(red.Ddel), 'Sp': red.Sp, 'Ip': sorted(red.Ip), 'states': st}
