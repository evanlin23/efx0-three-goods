"""reduce4.run with the extension search in C (k4/reduce4c.c), for reductions whose extension spaces are too large for
reduce4's Python enumeration (two-agent gadgets: k4/TWINS.md, attempts/k4-twins-claw.md).

Division of labour:
  - Python (reduce4): the local states, their admissible profiles (adm_array), and, for every extension the C program
    proposes, the rebuilt extension (X_S, X_O), its domination (reduce4.Reduction.dominated, and the moved-items test of
    reduce4.Reduction.extensions), its views and safe masks (reduce4.views_of, reduce4.safe_mask). A proposal that fails
    any of these raises an error. So the C program only decides which extensions are looked at.
  - C: enumerates the same extensions as reduce4.Reduction.extensions and prints one per distinct tuple of views whose
    safe sets are nonempty.
run() returns (reduced-profile array, kept) in reduce4.run's format, so reduce4.select and reduce4.record write the
certificate unchanged, and k4/check_reductions4.py (through k4/check_twins4.py) re-checks it as usual.
test(): agreement with reduce4.run on reductions small enough for both.
Usage: reduce4c.py test"""
import os, sys, subprocess, itertools, tempfile
import numpy as np
from multiprocessing import Pool
import reduce4 as R4

HERE = os.path.dirname(os.path.abspath(__file__))
BIN = os.environ.get('REDUCE4C_BIN', os.path.join(tempfile.gettempdir(), 'reduce4c_bin'))


def build():
    src = os.path.join(HERE, 'reduce4c.c')
    if not os.path.exists(BIN) or os.path.getmtime(BIN) < os.path.getmtime(src):
        subprocess.run(['gcc', '-O2', '-o', BIN, src], check=True)
    return BIN


class Enc:
    """Good indices of a reduction: local goods, interior goods, markers w:<gadget agent> and W:<k>."""

    def __init__(self, red):
        cfg = red.cfg
        names = sorted(red.L) + sorted(cfg.I) + ['w:' + s for s in red.sps] + ['W:%d' % k for k in range(len(red.L) + 2)]
        assert len(names) <= 64
        self.idx = {g: i for i, g in enumerate(names)}
        self.red = red
        mask = lambda gs: sum(1 << self.idx[g] for g in gs)
        self.umask = mask([g for g in names if g in cfg.D or R4.is_marker(g)])
        self.imask = mask(cfg.I)
        self.ipmask = mask(red.Ip)
        self.Ig = sorted(cfg.I)

    def header(self):
        cfg = self.red.cfg
        out = ['%d %d %d %d' % (len(self.idx), self.umask, self.imask, self.ipmask),
               ' '.join(map(str, [len(self.Ig)] + [self.idx[g] for g in self.Ig])), str(len(cfg.agents))]
        for s in cfg.agents:
            R = cfg.S[s]
            out.append(' '.join(map(str, [len(R)] + [self.idx[g] for g in R] + [len(cfg.dom[s])])))
            out.append(' '.join(str(int(x)) for t in cfg.dom[s] for x in t))
        return '\n'.join(out) + '\n'

    def bm(self, B):
        return sum(1 << self.idx[x] for x in B)

    def state(self, Yb, Ob, src):
        sps = sorted(Yb)
        sk, si = (-1, 0) if src is None else ((0, sps.index(src[1])) if src[0] == 'sp' else (1, src[1]))
        moved = [x for s in sps for x in Yb[s] if x not in self.red.Ip]
        return ' '.join(map(str, [len(sps)] + [self.bm(Yb[s]) for s in sps] + [len(Ob)] + [self.bm(b) for b in Ob] +
                            [sk, si, len(moved)] + [self.idx[x] for x in moved])) + '\n'


def rebuild(red, Yb, Ob, src, dests, chs):
    """The extension (X_S, X_O) of reduce4.Reduction.extensions with these choices, checked as reduce4 checks it."""
    cfg = red.cfg
    S = cfg.agents
    Yall = list(Yb.values()) + Ob
    Ysrc = None if src is None else (Yb[src[1]] if src[0] == 'sp' else Ob[src[1]])
    moved = [x for s in sorted(Yb) for x in Yb[s] if x not in red.Ip]
    ipblocks = [k for k, b in enumerate(Ob) if any(x in red.Ip for x in b) or src == ('O', k)]
    free = [k for k in ipblocks if not red.U(Ob[k]) and any(x in red.Ip for x in Ob[k])]
    dest = S + [('O', k) for k in free]
    choices = S + [('O', k) for k in ipblocks]
    Xs = {s: [] for s in S}
    Ox = [[x for x in b if x not in red.Ip] for b in Ob]
    for x, d in zip(moved, dests):
        d = dest[d]
        (Ox[d[1]] if isinstance(d, tuple) else Xs[d]).append(x)
    Udom = [red.U(B) for B in Yall] + ([red.U(Ysrc)] if Ysrc is not None else [])
    assert not any(len(red.U(B)) >= 2 and not any(red.U(B) <= u for u in Udom) for B in list(Xs.values()) + Ox), \
        'C proposal fails the moved-items test'
    for g, c in zip(sorted(cfg.I), chs):
        c = choices[c]
        (Ox[c[1]] if isinstance(c, tuple) else Xs[c]).append(g)
    assert all(red.dominated(Xs[s], Yall, Ysrc) for s in S), 'C proposal: an S bundle is not dominated'
    assert all(red.dominated(Ox[k], Yall, Ysrc) for k in ipblocks), 'C proposal: an outside bundle is not dominated'
    return Xs, Ox


def _chunk(args):
    red, sts = args
    enc = Enc(red)
    inp = enc.header() + ''.join(enc.state(*st) for st, _ in sts)
    out = subprocess.run([build()], input=inp, capture_output=True, text=True, check=True).stdout.split('\n')
    cfg = red.cfg
    res, pos = [], 0
    for st, A in sts:
        k = int(out[pos].split()[1]); pos += 1
        seen, items = set(), []
        for line in out[pos:pos + k]:
            a, b = line.split('|')
            X = rebuild(red, *st, [int(x) for x in a.split()], [int(x) for x in b.split()])
            vw = R4.views_of(cfg, *X)
            if vw in seen: continue
            seen.add(vw)
            masks = [R4.safe_mask(cfg, s, v) for s, v in zip(cfg.agents, vw)]
            if all(m.any() for m in masks): items.append((masks, X))
        pos += k
        items.sort(key=lambda it: -int(np.prod([m.sum() for m in it[0]])))
        keep = []
        for masks, X in items:
            if not any(all((m & ~kk).sum() == 0 for m, kk in zip(masks, km)) for km, _ in keep): keep.append((masks, X))
        res.append((st, A, keep))
    return res


def run(red, jobs=4, chunk=400):
    """reduce4.run with the C extension search: (reduced-profile array, kept)."""
    build()
    cfg = red.cfg
    sts = []
    for st in red.states():
        A = R4.adm_array(cfg, red.admissible(*st))
        if A is not None: sts.append((st, A))
    parts = [(red, sts[i:i + chunk]) for i in range(0, len(sts), chunk)]
    if jobs > 1:
        with Pool(jobs) as pool: outs = pool.map(_chunk, parts)
    else:
        outs = [_chunk(p) for p in parts]
    bad = np.zeros(cfg.shape, dtype=bool)
    kept = []
    for part in outs:
        for st, A, items in part:
            cov = np.zeros(cfg.shape, dtype=bool)
            for masks, _ in items: cov |= R4.outer(masks)
            bad |= A & ~cov
            kept.append((st, A, items))
    return ~bad, kept


def test(jobs=4):
    """Agreement with reduce4.run (reduced arrays, and per state the union of the kept extensions' coverage)."""
    import time, mincex4 as M, twins4 as T
    cases = []
    cfg = M.config('pair', 'P3', 'P3'); cases += [(cfg, r) for r in M.reductions(cfg, 'pair')]
    cfg = M.config('loop', 'P3', 'P3'); cases += [(cfg, r) for r in M.reductions(cfg, 'loop')]
    cfg = M.px_config('Q3'); cases.append((cfg, R4.Reduction(cfg, 'DEL', {}, set(), source=True)))
    cfg = M.px_config('Q3'); cases.append((cfg, R4.Reduction(cfg, 'GAD', {'h': ('fix', {'a': 2, 'b': 2, "z'": 3})}, {"z'"}, source=True)))
    cfg = T.CONFIGS['dbl-Q3-P4'](); cases.append((cfg, R4.Reduction(cfg, 'GAD', {'h': ('fix', {'a': 2, 'x': 4, "z0'": 1})}, {"z0'"}, source=True)))
    cfg = T.CONFIGS['dbl-Q3-Q3'](); cases += [(cfg, r) for r in T.drop_gadget(cfg)]
    cfg = T.claw_config(); cases.append((cfg, R4.Reduction(cfg, 'DEL', {}, set(), source=True)))
    cfg = T.claw_config(); cases.append((cfg, R4.Reduction(cfg, 'GAD', {'h': ('fix', {'y1': 0, 'y2': 2, 'y3': 2, "z0'": 1})}, {"z0'"}, source=True)))
    cfg = T.CONFIGS['tri-Q3-Q3-Q3'](); cases.append((cfg, R4.Reduction(cfg, 'GAD', {'h': ('fix', {'a1': 2, 'a2': 2, 'a3': 2, "z0'": 3})}, {"z0'"}, source=True)))
    ok_all = True
    for cfg, red in cases:
        t = time.time(); ok1, k1 = R4.run(red, jobs); t1 = time.time() - t
        t = time.time(); ok2, k2 = run(red, jobs); t2 = time.time() - t
        same = (ok1 == ok2).all() and len(k1) == len(k2)
        if same:
            c1 = {R4.canon(*st)[0]: (A, items) for st, A, items in k1}
            for st, A, items in k2:
                A1, it1 = c1[R4.canon(*st)[0]]
                cv1 = np.zeros(cfg.shape, dtype=bool); cv2 = np.zeros(cfg.shape, dtype=bool)
                for m, _ in it1: cv1 |= R4.outer(m)
                for m, _ in items: cv2 |= R4.outer(m)
                if not ((A1 == A).all() and (cv1 == cv2).all()): same = False; break
        ok_all &= same
        print('  %-14s %-34s reduce4 %6d (%5.1f s)  reduce4c %6d (%5.1f s)  %s' % (
            cfg.name, red.name[:34], ok1.sum(), t1, ok2.sum(), t2, 'agree' if same else 'DISAGREE'), flush=True)
    print('RESULT: %s' % ('OK' if ok_all else 'FAILED'))
    return ok_all


if __name__ == '__main__':
    if sys.argv[1:2] == ['test']:
        sys.exit(0 if test() else 1)


def _cover_chunk(args):
    """Coverage arrays (packed) of every state in the chunk, from the C proposals rebuilt and checked by reduce4."""
    red, sts = args
    res = _chunk((red, [(st, None) for st in sts]))
    cfg = red.cfg
    out = []
    for st, _, items in res:
        cov = np.zeros(cfg.shape, dtype=bool)
        for masks, _ in items: cov |= R4.outer(masks)
        out.append(np.packbits(cov.ravel()))
    return out


def gadget_search2(cfg, spec, Ip, jobs=4, chunk=400):
    """Two (or more) fixed gadget agents, each with a menu of valuations: spec = [(name, goods, M)] with M a rows x
    len(goods) array. Coverage of a local state does not depend on the gadget valuations, so it is computed once per
    state (C search, reduce4 check); admissibility is the conjunction of one menu vector per gadget agent
    (reduce4.menu_admissible). Returns ok[i1, i2, ..., profile]: the valuation choice reduces the profile."""
    build()
    Sp = {name: ('fix', dict(zip(goods, M[0]))) for name, goods, M in spec}
    red = R4.Reduction(cfg, 'search2', Sp, Ip, source=True)
    sts = list(red.states())
    parts = [(red, sts[i:i + chunk]) for i in range(0, len(sts), chunk)]
    if jobs > 1:
        with Pool(jobs) as pool: covs = [c for part in pool.map(_cover_chunk, parts) for c in part]
    else:
        covs = [c for p in parts for c in _cover_chunk(p)]
    P = int(np.prod(cfg.shape))
    unc = 1.0 - np.unpackbits(np.array(covs), axis=1)[:, :P].astype(np.float32)          # states x P
    adms = [np.array([R4.menu_admissible(goods, M, *st, name) for st in sts], dtype=np.float32) for name, goods, M in spec]
    assert len(spec) == 2, 'two gadget agents'
    A1, A2 = adms
    ok = np.zeros((A1.shape[1], A2.shape[1], P), dtype=bool)
    for i in range(A1.shape[1]):
        W = A2 * A1[:, i:i + 1]                                                          # states x M2
        ok[i] = ~((W.T @ unc) > 0.5)
    return ok, len(sts)
