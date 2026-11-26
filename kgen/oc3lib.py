"""Python side of kgen/oc3.c (brute force for OC1 and its variants with n = 3 agents, any k), plus the second,
independent check through k4/sdc's SAT code (sdclib.Enc, oc_absorb.extends_A, de_free.moves with unbounded sets).

    from oc3lib import brute, sat_check, picks
    brute(v)      -> per order (6, in ORD): dict of counts NONE, CODE, STRICT, FREE0, FREEOC, MD, EFX and a CODE witness
    sat_check(v)  -> per order: 0 (picks have a one-absorber completion), 1 (one chain, t >= 0, then one), None (neither)

v is a list of three lists of m nonnegative integers (v[i][g]).  Orders are the permutations of (0, 1, 2) in
lexicographic order.  Build: gcc -O2 -shared -fPIC -o kgen/liboc3.so kgen/oc3.c (done on import if missing)."""
import os, sys, ctypes, itertools, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
ORD = list(itertools.permutations(range(3)))
KEYS = ['NONE', 'CODE', 'STRICT', 'FREE0', 'FREEOC', 'MD', 'EFX']

_lib = None


def lib():
    global _lib
    if _lib is None:
        so = os.path.join(HERE, 'liboc3.so'); src = os.path.join(HERE, 'oc3.c')
        if not os.path.exists(so) or os.path.getmtime(so) < os.path.getmtime(src):
            tmp = so + '.%d.tmp' % os.getpid()      # build aside, then rename: running users keep the old inode
            subprocess.check_call(['gcc', '-O2', '-march=native', '-shared', '-fPIC', '-o', tmp, src])
            os.replace(tmp, so)
        _lib = ctypes.CDLL(so)
        _lib.oc3.argtypes = [ctypes.c_int, ctypes.POINTER(ctypes.c_longlong), ctypes.POINTER(ctypes.c_longlong),
                             ctypes.POINTER(ctypes.c_int)]
        _lib.oc3p.argtypes = _lib.oc3.argtypes + [ctypes.POINTER(ctypes.c_ulonglong)]
    return _lib


def brute(v):
    m = len(v[0]); assert len(v) == 3 and all(len(r) == m for r in v) and m <= 20
    arr = (ctypes.c_longlong * (3 * m))(*[int(x) for r in v for x in r])
    out = (ctypes.c_longlong * 48)(); wit = (ctypes.c_int * 18)()
    lib().oc3(m, arr, out, wit)
    res = []
    for o in range(6):
        d = {k: out[o * 8 + t] for t, k in enumerate(KEYS)}
        w = [wit[o * 3 + i] for i in range(3)]
        d['wit'] = None if w[0] < 0 else [[g for g in range(m) if w[i] >> g & 1] for i in range(3)]
        res.append(d)
    return res


def shapes(v):
    """per order: the set of (shape, absorber) realized by some EFX0 allocation under the one-absorber completion.
    shape: ('none',), ('t0', x), ('t1', x0, x1), ('t2', x0, x1, x2); absorber: an agent, or None"""
    m = len(v[0])
    arr = (ctypes.c_longlong * (3 * m))(*[int(x) for r in v for x in r])
    out = (ctypes.c_longlong * 48)(); wit = (ctypes.c_int * 18)(); pat = (ctypes.c_ulonglong * 6)()
    lib().oc3p(m, arr, out, wit, pat)
    names = [('none',)] + [('t0', x) for x in range(3)] + \
            [('t1', x0, x1) for x0 in range(3) for x1 in range(3) if x1 != x0] + [('t2',) + p for p in ORD]
    res = []
    for o in range(6):
        res.append({(names[b // 4], (b % 4) if b % 4 < 3 else None) for b in range(64) if pat[o] >> b & 1})
    return res


def picks(v, order):
    m = len(v[0]); left = set(range(m)); y = [None] * 3
    for i in order:
        av = [g for g in range(m) if g in left and v[i][g] > 0]
        if av:
            g = max(av, key=lambda h: (v[i][h], -h)); y[i] = g; left.discard(g)
    return y


def efx0(v, X):
    for i in range(3):
        own = sum(v[i][g] for g in X[i])
        for j in range(3):
            if j != i and len(X[j]) >= 2:
                if sum(v[i][g] for g in X[j]) - min(v[i][g] for g in X[j]) > own: return False
    return True


def sat_check(v, which=None):
    """the second check: k4/sdc's own OC1 test (oc_absorb.py), with chains of de_free.py and no cap on |H|"""
    sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
    import _paths  # noqa
    import de_free as DF
    from sdclib import Enc
    from oc_absorb import extends_A
    from sdc_orders import sd
    m = len(v[0])
    DF.CHAIN_ONLY = True; DF.HMAX = m; DF.BMAX = m
    sets = [[g for g in range(m) if v[i][g] > 0] for i in range(3)]
    vals = [[v[i][g] for g in sets[i]] for i in range(3)]
    E = Enc(sets, vals, m); res = []
    for k, o in enumerate(ORD):
        if which is not None and k not in which: res.append('skip'); continue
        Y = sd(E, list(o))[0]
        base = [-1] * m
        for i, g in enumerate(Y):
            if g is not None: base[g] = i
        base = tuple(base)
        if extends_A(E, base, 1): res.append(0)
        elif any(extends_A(E, b2, 1) for b2 in set(DF.iter_chains(E, base))): res.append(1)
        else: res.append(None)
    return res


def status(d):
    """chains OC1 needs for one order from brute()'s counts: 0, 1, or None (OC1 fails)"""
    return 0 if d['NONE'] else (1 if d['CODE'] else None)
