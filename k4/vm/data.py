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
            k = min(kmax, rng.choice([1, 2, 3, 4, 4, 4, 3, 3] + ([5, 5, 5] if kmax >= 5 else [])))
            S = rng.sample(range(m), min(k, m))
            V = [rng.randint(1, vmax) for _ in S] if ties else rng.sample(range(1, vmax + 1), len(S))
            sets.append(S); vals.append(V)
        out.append(('gen:%d' % t, sets, vals, m))
    return out


def named(ext):
    """the coordinator's named hard instances: B< and B> (OC1 counterexample on a strict connected n = 6 core),
    SPECIAL, lb4-owner-needs-from-base-n4m8, and the TTC session's 84 OC1 counterexamples, n = 5 counterexample and
    core candidate (json files extracted from claude/k4-ttc into the directory ext)"""
    B = [[0, 2, 3, 1], [6, 4, 5, 9], [1, 2, 3, 9], [1, 6, 7, 8], [3, 6, 9], [1, 3, 6, 9]]
    out = [('B<', B, [[6, 14, 16, 12], [4, 18, 12, 28], [28, 4, 16, 21], [16, 14, 12, 6], [28, 8, 24], [20, 30, 8, 4]], 10),
           ('B>', B, [[6, 14, 16, 12], [4, 18, 12, 28], [28, 4, 16, 19], [16, 14, 12, 6], [28, 8, 24], [20, 30, 8, 4]], 10)]
    out += special()
    d = json.load(open(os.path.join(ROOT, 'k4/suite/instances/lb4-owner-needs-from-base-n4m8.json')))
    out.append(('lb4-owner-needs-from-base-n4m8', d['sets'], d['vals'], d.get('m') or 1 + max(max(x) for x in d['sets'])))
    for t, x in enumerate(json.load(open(os.path.join(ext, 'oc1_counterexamples.json')))):
        out.append(('ttc84:%d' % t, x['sets'], x['vals'], x['m']))
    for fn in ('oc1_counterexample_n5.json', 'oc1_core_candidate.json'):
        x = json.load(open(os.path.join(ext, fn)))
        x = x[0] if isinstance(x, list) else x
        out.append((fn[:-5], x['sets'], x['vals'], x.get('m') or 1 + max(max(s) for s in x['sets'])))
    out.append(('vmx-cex-n3', [[0, 1, 2, 5], [1, 3, 4, 5], [2, 3, 4, 5]], [[4, 3, 2, 8], [4, 7, 2, 8], [4, 8, 3, 10]], 6))
    out.append(('vmx-cex-n4', [[0, 1, 2, 6], [1, 2, 5, 7], [3, 4, 5, 6], [3, 4, 7]], [[2, 7, 4, 8], [4, 2, 8, 7], [6, 3, 10, 2], [3, 2, 4]], 8))
    return out


def _dense(rows):
    sets = [[g for g, x in enumerate(r) if x > 0] for r in rows]
    vals = [[x for x in r if x > 0] for r in rows]
    return sets, vals, len(rows[0])


def k5():
    """the k = 5 instances of the k-sensitivity session (k4/ksens.md on claude/k4-ksens: PW5 and its k = 4 version,
    RD5 and its k = 4 version, sections 1 and 6) and the general-k session's n = 4 OC1 counterexamples
    (attempts/kgen-n4-oc1.md on claude/kgen-n3: the strict one with m = 8 and the one with ties, m = 7)"""
    out = [('PW5', [[0, 5, 6, 7, 8], [1, 5, 6, 7, 8], [2, 5, 6, 7, 8], [0, 1, 2, 3], [0, 1, 2, 4]],
            [[10, 9, 8, 7, 6]] * 3 + [[6, 4, 2, 1], [6, 4, 2, 1]], 9),
           ('PW4', [[0, 5, 6, 7], [1, 5, 6, 7], [2, 5, 6, 7], [0, 1, 2, 3], [0, 1, 2, 4]],
            [[10, 9, 8, 7]] * 3 + [[6, 4, 2, 1], [6, 4, 2, 1]], 8),
           ('RD5', [[0, 3, 4, 5, 1], [1, 2, 3], [1, 3, 4, 2], [0, 2, 6, 5]],
            [[26, 44, 24, 33, 57], [12, 11, 6], [9, 6, 1, 8], [36, 53, 4, 47]], 7),
           ('RD4', [[0, 3, 5, 1], [1, 2, 3], [1, 3, 4, 2], [0, 2, 6, 5]],
            [[26, 44, 33, 57], [12, 11, 6], [9, 6, 1, 8], [36, 53, 4, 47]], 7)]
    s1, v1, m1 = _dense([[34, 0, 0, 0, 38, 35, 37, 33], [0, 10, 5, 0, 0, 4, 2, 0], [0, 2, 0, 0, 3, 0, 1, 0], [52, 54, 53, 4, 0, 0, 0, 51]])
    s2, v2, m2 = _dense([[0, 155, 1, 0, 0, 155, 0], [0, 75, 2, 74, 0, 74, 77], [0, 0, 0, 2, 133, 0, 134], [1, 4, 0, 2, 0, 0, 0]])
    out += [('kgen-n4-strict', s1, v1, m1), ('kgen-n4-ties', s2, v2, m2)]
    return out
