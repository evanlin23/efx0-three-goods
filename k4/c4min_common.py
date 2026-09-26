"""Shared helpers for the C4min hunt tools (k4/c4min_hunt.md): core lists, input text for k4/c4min_hunt.c and
k4/c4x.c, compiled binaries. Types are the strict balanced types of k4/check4.py (core_domains), as every k = 4 tool
uses."""
import gzip, hashlib, json, os, subprocess, sys, tempfile, threading

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
from check4 import core_domains, is_core  # noqa: E402


def _compile(src_bytes, name, extra=()):
    path = os.path.join(tempfile.gettempdir(), name + '_' + hashlib.sha1(src_bytes).hexdigest()[:12])
    if not os.path.exists(path):          # compile under a private name, then rename (safe with parallel callers)
        tmp = f'{path}.{os.getpid()}.{threading.get_ident()}'
        with open(tmp + '.c', 'wb') as f: f.write(src_bytes)
        subprocess.run(['gcc', '-O2', '-march=native', *extra, '-o', tmp, tmp + '.c'], check=True)
        os.replace(tmp, path)
    return path


def hunt_binary():
    """k4/c4min_hunt.c (C4MIN_HUNT_BIN overrides)."""
    if os.environ.get('C4MIN_HUNT_BIN'): return os.environ['C4MIN_HUNT_BIN']
    return _compile(open(os.path.join(HERE, 'c4min_hunt.c'), 'rb').read(), 'c4min_hunt')


def c4x_binary():
    """k4/c4x.c of PR #36 (C4X_BIN overrides)."""
    if os.environ.get('C4X_BIN'): return os.environ['C4X_BIN']
    return _compile(open(os.path.join(HERE, 'c4x.c'), 'rb').read(), 'c4x')


def load_cores(path):
    data = json.load(gzip.open(path, 'rt'))
    cores = data['cores'] if isinstance(data, dict) else data
    return [{'n': c['n'], 'm': c['m'], 'sets': c['sets']} for c in cores]


def domains(sets, m):
    return core_domains(sets, m, False)


def input_all(sets, m, doms, order=None):
    """input text for c4min_hunt.c / c4x.c with every type of every agent (agents in `order`)."""
    order = order if order is not None else list(range(len(sets)))
    lines = [f'{len(sets)} {m}']
    for i in order:
        S, D = sets[i], doms[i]
        lines.append(f'{len(S)} ' + ' '.join(map(str, S)) + f' {len(D)}')
        for vals in D: lines.append(' '.join(str(vals[g]) for g in S))
    return '\n'.join(lines) + '\n'


def input_one(sets, m, vals):
    """input text for one profile (one type per agent; vals[i] = dict good -> value)."""
    lines = [f'{len(sets)} {m}']
    for S, v in zip(sets, vals):
        lines.append(f'{len(S)} ' + ' '.join(map(str, S)) + ' 1')
        lines.append(' '.join(str(v[g]) for g in S))
    return '\n'.join(lines) + '\n'


def hunt_one(sets, m, vals, opts=()):
    """c4min_hunt.c -1 on one profile: dict fstar, dstar, valid, minfrozen, good, completable, sigma, defsum (the sum
    over all valid P of min(def, 99), a checksum of every deficit)."""
    inp = input_one(sets, m, vals) + ' '.join('0' for _ in sets) + '\n'
    out = subprocess.run([hunt_binary(), '-1', *opts], input=inp, capture_output=True, text=True, check=True).stdout
    w = out.split()
    assert w[0] == 'PROFILE', out
    r = {}
    for k in ('fstar', 'dstar', 'valid', 'minfrozen', 'good', 'completable', 'sigma', 'defsum'):
        r[k] = int(w[w.index(k) + 1])
    return r


def c4x_one(sets, m, vals, opts=()):
    """k4/c4x.c -1s -R -a on one profile: fstar, valid, minfrozen, good, dstar (as c4x reports them)."""
    inp = input_one(sets, m, vals) + '0 1\n'
    out = subprocess.run([c4x_binary(), '-1s', '-R', '-a', '-p', '6', *opts], input=inp, capture_output=True, text=True, check=True).stdout
    r = {}
    for line in out.splitlines():
        w = line.split()
        if w[0] == 'STREAM': r['valid'], r['fstar'], r['minfrozen'] = int(w[2]), int(w[4]), int(w[6])
        if w[0] == 'DEFICIT':
            r['good'] = int(line.split('with deficit <= 0: ')[1].split(',')[0].split()[0])
            r['dstar'] = int(line.split('least deficit seen ')[1])
    return r


def type_class(v):
    """order-type class (0-11) of a strict balanced 4-good type with values v: with a > b > c > d, the position of a
    among the pair sums c+d < b+d < b+c (0: a < c+d, 'flat'; 3: a > b+c), whether b > c+d, and whether a+d > b+c;
    numbered in the order of CLASSES."""
    a, b, c, d = sorted(v, reverse=True)
    return CLASSES.index((sum(a > x for x in (c + d, b + d, b + c)), b > c + d, a + d > b + c))


CLASSES = [(0, False, False), (0, False, True), (1, False, False), (1, False, True), (1, True, False), (1, True, True),
           (2, False, False), (2, False, True), (2, True, False), (2, True, True), (3, False, True), (3, True, True)]
