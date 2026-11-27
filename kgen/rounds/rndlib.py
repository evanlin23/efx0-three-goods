"""ctypes wrapper of kgen/rounds/rnd.c (ROUND+ checker, strictly positive additive values), plus the SD helper.

    import rndlib
    res = rndlib.analyze(vals)            # vals: n lists of m positive ints
    res -> list of dicts, one per distinct start: picks, order, counts {EXTF, EXT1, OC1, RNDF, RND1, MD}

Classes (kgen/rounds.md §1): EXTF/EXT1 picks extend (free / one absorber); OC1 one chain t >= 0 then one absorber;
RNDF/RND1 one round of vertex-disjoint chains then free / one-absorber completion; MD value domination.
"""
import ctypes, os, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
SO = os.path.join(HERE, 'librnd.so')
KINDS = ['EXTF', 'EXT1', 'OC1', 'RNDF', 'RND1', 'MD', 'RNDX', 'RNDX1', 'RNDP', 'RNDP1']
K = {k: i for i, k in enumerate(KINDS)}


def _build():
    src = os.path.join(HERE, 'rnd.c')
    if not os.path.exists(SO) or os.path.getmtime(SO) < os.path.getmtime(src):
        tmp = SO + '.%d.tmp' % os.getpid()      # build aside, then rename: running processes keep the old inode
        subprocess.check_call(['gcc', '-O2', '-march=native', '-shared', '-fPIC', '-o', tmp, src])
        os.replace(tmp, SO)


_build()
_L = ctypes.CDLL(SO)
LL = ctypes.c_longlong
_L.rnd_analyze.restype = ctypes.c_int
_L.rnd_witness.restype = ctypes.c_int
_L.rnd_list_efx.restype = LL
_L.rnd2_count.restype = LL
_L.rnd2_count_margin.restype = LL
_L.rnd_oc1z.restype = ctypes.c_int
_L.rnd_grid.restype = LL


def _arr(vals):
    n, m = len(vals), len(vals[0])
    return n, m, (LL * (n * m))(*[int(x) for row in vals for x in row])


def analyze(vals, cap=0, want=('RND1',), margin='RND1'):
    """cap = 0: count every witness; cap > 0: stop counting a class at cap and stop the enumeration once every
    start reached cap in every class of `want`."""
    n, m, A = _arr(vals)
    NS = 5040
    picks = (ctypes.c_int * (NS * n))(); order = (ctypes.c_int * (NS * n))()
    cnt = (LL * (NS * len(KINDS)))(); nefx = LL()
    wm = 0
    for w in want: wm |= 1 << K[w]
    _L.rnd_set_margin_kind(K[margin])
    ns = _L.rnd_analyze(n, m, A, LL(cap), wm, picks, order, cnt, ctypes.byref(nefx))
    if ns < 0: raise ValueError('instance too large')
    msum = (ctypes.c_double * NS)(); mmax = (ctypes.c_double * NS)()
    _L.rnd_margins(msum, mmax)
    out = []
    for s in range(ns):
        out.append({'picks': tuple(picks[s * n + a] for a in range(n)),
                    'order': tuple(order[s * n + a] for a in range(n)),
                    'counts': {k: cnt[s * len(KINDS) + i] for i, k in enumerate(KINDS)},
                    'msum': msum[s], 'mmax': mmax[s]})
    return out, nefx.value


def witness(vals, picks, kind):
    """first EFX allocation (owner list) witnessing `kind` from the start `picks`, with the chain info
    (succ, end flag, chain start per agent); None if none"""
    n, m, A = _arr(vals)
    P = (ctypes.c_int * n)(*picks); own = (ctypes.c_int * m)(); info = (ctypes.c_int * (3 * n))()
    ok = _L.rnd_witness(n, m, A, P, K[kind], own, info)
    if not ok: return None
    return list(own), {'succ': list(info[0:n]), 'end': list(info[n:2 * n]), 'start': list(info[2 * n:3 * n])}


def list_efx(vals, maxout=2000000):
    n, m, A = _arr(vals)
    buf = (ctypes.c_int * (maxout * m))()
    c = _L.rnd_list_efx(n, m, A, buf, LL(maxout))
    k = min(c, maxout)
    return [tuple(buf[i * m:(i + 1) * m]) for i in range(k)], c


def sd(vals, order):
    """serial-dictatorship picks with every good relevant (ties to the smaller good index)"""
    m = len(vals[0]); left = set(range(m)); Y = [None] * len(vals)
    for a in order:
        g = max(left, key=lambda h: (vals[a][h], -h)); Y[a] = g; left.discard(g)
    return Y


def rounds_needed(res, A1=True):
    """per start: 0 if the picks extend (EXT1 if A1 else EXTF), 1 if one round suffices, 2 for 'more'"""
    e, r = ('EXT1', 'RND1') if A1 else ('EXTF', 'RNDF')
    out = []
    for s in res:
        c = s['counts']
        out.append(0 if c[e] > 0 else (1 if c[r] > 0 else 2))
    return out


def two_rounds(vals, picks, cap=0):
    """number of complete EFX allocations reachable by at most two rounds from the start `picks` (free completion;
    rnd.c Lemma RC2), capped at cap (0 = all); returns (count, number of MD EFX allocations visited)"""
    n, m, A = _arr(vals)
    P = (ctypes.c_int * n)(*picks); md = LL()
    c = _L.rnd2_count(n, m, A, P, LL(cap), ctypes.byref(md))
    return c, md.value


def two_rounds_margin(vals, picks, cap=0):
    """(count, MD count, margin sum) for <= 2 rounds; the margin of a witness is min(EFX slack, the best two-round
    structure's smallest gain slack), each normalized by the agent's total value"""
    n, m, A = _arr(vals)
    P = (ctypes.c_int * n)(*picks); md = LL(); ms = ctypes.c_double()
    c = _L.rnd2_count_margin(n, m, A, P, LL(cap), ctypes.byref(md), ctypes.byref(ms))
    return c, md.value, ms.value


def oc1z(vals):
    """zero values allowed: per distinct start (zero-aware SD), perfect flag and, for perfect starts, counts of EFX0
    allocations witnessing EXT1 (picks extend, one absorber), OC1 (k4/sdc.md §29/§31 official move: addition, chain or
    ring, one absorber), MD, OC1P (OC1', §4.6), RND1Z (one plain round), RNDPZ (ROUND-P, §4.9) and RNDOZ (a round of
    OC1' moves: non-end agents take only their own chain end's goods; k4/sdc/roundp_check.py's form), plus margin sums
    (msum = ms_OC1: OC1 witnesses; ms_RND1Z, ms_RNDPZ: round witnesses)"""
    n, m, A = _arr(vals)
    NS = 5040
    picks = (ctypes.c_int * (NS * n))(); order = (ctypes.c_int * (NS * n))(); perf = (ctypes.c_int * NS)()
    cnt = (LL * (NS * 6))(); ms = (ctypes.c_double * NS)(); nefx = LL()
    ns = _L.rnd_oc1z(n, m, A, picks, order, perf, cnt, ms, ctypes.byref(nefx))
    rm = (ctypes.c_double * (2 * NS))(); _L.rnd_oc1z_rmargins(rm)
    c1p = (LL * NS)(); _L.rnd_oc1z_c1p(c1p)
    out = []
    for s in range(ns):
        out.append({'picks': tuple(picks[s * n + a] for a in range(n)), 'order': tuple(order[s * n + a] for a in range(n)),
                    'perfect': bool(perf[s]), 'EXT1': cnt[s * 6], 'OC1': cnt[s * 6 + 1], 'MD': cnt[s * 6 + 2],
                    'OC1P': cnt[s * 6 + 3], 'RND1Z': cnt[s * 6 + 4], 'RNDPZ': cnt[s * 6 + 5], 'msum': ms[s],
                    'ms_OC1': ms[s], 'ms_OC1P': ms[s], 'ms_RND1Z': rm[2 * s], 'ms_RNDPZ': rm[2 * s + 1],
                    'RNDOZ': c1p[s], 'ms_RNDOZ': rm[2 * s + 1]})
    return out, nefx.value


def grid(n, m, V, maxrec=20, limit=0):
    """exhaustive: every profile with values in {1..V} (rows as a multiset): (profiles, starts, starts failing one round,
    starts failing two rounds, list of (vals, picks) for two-round failures)"""
    out = (LL * 5)(); rec = (LL * (maxrec * (n * m + n)))()
    _L.rnd_grid(n, m, V, out, rec, maxrec, LL(limit))
    recs = []
    for r in range(out[4]):
        base = r * (n * m + n)
        vals = [[rec[base + i * m + g] for g in range(m)] for i in range(n)]
        recs.append((vals, [rec[base + n * m + a] for a in range(n)]))
    return out[0], out[1], out[2], out[3], recs
