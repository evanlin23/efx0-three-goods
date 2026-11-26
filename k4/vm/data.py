"""Test data for k4/vm: the screen set, the suite, nof_var.SPECIAL, the hard profiles in results/k4_sdc/*.log,
random strict profiles of the certified k = 4 cores, and random general 4-limited instances (junk, top-heavy agents,
agents with fewer than three goods).  Every item: (name, sets, vals, m)."""
import os, sys, re, glob, json, gzip, random, itertools

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
SDC = os.path.join(ROOT, 'k4', 'sdc')
DE4 = os.path.join(ROOT, 'k4', 'de4')


def _sdc():
    for p in (SDC, DE4, os.path.join(ROOT, 'k3')):
        if p not in sys.path:
            sys.path.insert(0, p)


def screen():
    _sdc()
    import sdc_need
    return sdc_need.instances('screen')


def suite():
    _sdc()
    import sdc_need
    return sdc_need.instances('suite')


def special():
    _sdc()
    import nof_var
    return [(n, s, v, m) for n, s, v, m in nof_var.SPECIAL]


PAT = re.compile(r"sets\W{0,4}(\[\[[0-9,\s\[\]]*\]\])\W{0,8}vals\W{0,4}(\[\[[0-9,\s\[\]]*\]\])")


def logs():
    """every (sets, vals) pair printed in results/k4_sdc/*.log and results/k4_sdc/seeds_*.jsonl, deduplicated"""
    seen = set(); out = []
    for f in sorted(glob.glob(os.path.join(ROOT, 'results', 'k4_sdc', '*.log'))):
        txt = open(f, errors='replace').read()
        for a, b in PAT.findall(txt):
            try:
                sets = json.loads(a); vals = json.loads(b)
            except Exception:
                continue
            key = json.dumps([sets, vals])
            if key in seen or len(sets) != len(vals) or any(len(x) != len(y) for x, y in zip(sets, vals)):
                continue
            seen.add(key)
            m = 1 + max(max(x) for x in sets if x)
            out.append(('log:%s:%d' % (os.path.basename(f)[:-4], len(out)), sets, vals, m))
    for f in sorted(glob.glob(os.path.join(ROOT, 'results', 'k4_sdc', 'seeds_*.jsonl'))):
        for line in open(f):
            line = line.strip()
            if not line:
                continue
            sets, vals = json.loads(line)[:2]
            key = json.dumps([sets, vals])
            if key in seen:
                continue
            seen.add(key)
            out.append(('seed:%s:%d' % (os.path.basename(f), len(out)), sets, vals, 1 + max(max(x) for x in sets)))
    return out


CORE_FILES = {
    3: ['k4_certs_2.json.gz', 'k4_certs_3.json.gz'],
    4: ['k4_certs_4_n4_1.json.gz', 'k4_certs_4_n4_2.json.gz', 'k4_certs_4_n4_3.json.gz', 'k4_certs_4_pure.json.gz'],
    5: ['k4_certs_5_n4_1.json.gz', 'k4_certs_5_n4_2.json.gz', 'k4_certs_5_n4_3.json.gz', 'k4_certs_5_n4_4.json.gz',
        'k4_certs_5_pure.json.gz'],
    6: ['k4_certs_6_n4_1.json.gz'],
}
_cores = {}


def cores(key):
    if key not in _cores:
        cs = []
        for fn in CORE_FILES[key]:
            p = os.path.join(ROOT, 'results', fn)
            if os.path.exists(p):
                cs += [c['sets'] for c in json.load(gzip.open(p))['cores']]
        _cores[key] = cs
    return _cores[key]


def strict_types(k, maxv=16):
    """one integer representative per strict balanced order type of k goods (as k4/de4/de4lib.py)"""
    reps = {}
    subs = [S for r in range(1, k + 1) for S in itertools.combinations(range(k), r)]
    for vals in itertools.combinations(range(maxv, 0, -1), k):
        vals = list(vals)
        if k >= 2 and vals[0] >= sum(vals[1:]):
            continue
        sums = {S: sum(vals[t] for t in S) for S in subs}
        if len(set(sums.values())) != len(sums):
            continue
        key = tuple(sums[S] > sums[T] for S in subs for T in subs if not set(S) & set(T))
        if key not in reps or max(vals) < max(reps[key]):
            reps[key] = vals
    return sorted(reps.values())


TYPES = {3: strict_types(3), 4: strict_types(4)}


def random_core_profile(sets, rng):
    vals = []
    for S in sets:
        T = rng.choice(TYPES[len(S)]); perm = list(S); rng.shuffle(perm)
        d = dict(zip(perm, T)); vals.append([d[g] for g in S])
    return vals


def random_cores(key, N, seed):
    rng = random.Random(seed); cs = cores(key); out = []
    for t in range(N):
        sets = rng.choice(cs)
        out.append(('core%d:%d' % (key, t), sets, random_core_profile(sets, rng), 1 + max(max(x) for x in sets)))
    return out


def random_general(N, seed, nmin=2, nmax=6, mmax=10, vmax=20, ties=False, kmax=4):
    """general 4-limited instances: each agent values 1..4 random goods with random integer values in 1..vmax
    (distinct within an agent unless ties), some goods valued by nobody"""
    rng = random.Random(seed); out = []
    for t in range(N):
        n = rng.randint(nmin, nmax); m = rng.randint(n, mmax)
        sets = []; vals = []
        for i in range(n):
            k = min(kmax, rng.choice([1, 2, 3, 4, 4, 4, 3, 3]))
            S = rng.sample(range(m), min(k, m))
            V = [rng.randint(1, vmax) for _ in S] if ties else rng.sample(range(1, vmax + 1), len(S))
            sets.append(S); vals.append(V)
        out.append(('gen:%d' % t, sets, vals, m))
    return out
