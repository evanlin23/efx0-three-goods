"""Cross-check rnd.c (backward characterization) against
  (a) bruter.py (independent forward simulation, pure Python; small instances), and
  (b) k4/ksens/ocsat.py (SAT; branch claude/k4-ksens at 63089336; set KSENS to a checkout of that branch),
per start, on the classes EXTF, EXT1, OC1, RNDF, RND1, MD.

    python3 kgen/rounds/xcheck.py brute T SEED          # n = 3, m = 4..7 and n = 4, m = 4..6, mixed value kinds
    python3 kgen/rounds/xcheck.py sat T SEED nmin nmax mmin mmax
    python3 kgen/rounds/xcheck.py known                 # PW5 / RD5 lifted and the other named instances (SAT)
"""
import sys, os, random, json, itertools, collections, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import rndlib, bruter, families

MAP = {'EXTF': 'ext_free', 'EXT1': 'ext_1', 'OC1': 'oc1', 'RNDF': 'rnd_free', 'RND1': 'rnd_1'}


def gen(rng, n, m):
    kind = rng.choice(['generic', 'small', 'ident', 'near', 'twotype', 'tops'])
    if kind == 'generic': V = [rng.sample(range(1, 1000), m) for _ in range(n)]
    elif kind == 'small': V = [[rng.randint(1, 4) for _ in range(m)] for _ in range(n)]
    elif kind == 'ident':
        r = rng.sample(range(1, 100), m); V = [list(r) for _ in range(n)]
    elif kind == 'near':
        r = [rng.randint(20, 60) for _ in range(m)]; V = [[max(1, x + rng.randint(-3, 3)) for x in r] for _ in range(n)]
    elif kind == 'twotype':
        a = rng.sample(range(1, 100), m); b = rng.sample(range(1, 100), m)
        V = [list(a) if rng.random() < 0.5 else list(b) for _ in range(n)]
    else:
        V = [[rng.randint(5, 12) for _ in range(m)] for _ in range(n)]
        for i in range(n): V[i][i] = 40
    return kind, V


def c_classes(V):
    res, _ = rndlib.analyze(V)
    return {s['picks']: {k: s['counts'][k] > 0 for k in ['EXTF', 'EXT1', 'OC1', 'RNDF', 'RND1', 'MD']} for s in res}


def run_brute(T, seed):
    rng = random.Random(seed); C = collections.Counter(); bad = 0
    for t in range(T):
        n = rng.choice([3, 3, 4]); m = rng.randint(n + 1, 7 if n == 3 else 6)
        kind, V = gen(rng, n, m)
        cc = c_classes(V); seen = set()
        for o in itertools.permutations(range(n)):
            Y = tuple(bruter.sd(V, o))
            if Y in seen: continue
            seen.add(Y)
            b = bruter.classify(V, o)
            for k, bk in MAP.items():
                C[(k, cc[Y][k])] += 1
                if cc[Y][k] != b[bk]:
                    bad += 1; print('MISMATCH', k, json.dumps(V), o, cc[Y][k], b[bk], flush=True)
        C['starts'] += len(seen)
    for k in sorted(C, key=str): print(k, C[k])
    print('mismatches', bad)


def ksens_mods():
    ks = os.environ.get('KSENS', '/tmp/claude-0/-home-user-efx0-three-goods/1bef8951-d60e-5a6c-a841-d862b0933832/scratchpad/ksens')
    sys.path.insert(0, os.path.join(ks, 'k4', 'ksens')); sys.path.insert(0, os.path.join(ks, 'k4', 'sdc'))
    import ocsat
    return ocsat


def sat_classes(ocsat, V):
    n, m = len(V), len(V[0]); sets = [list(range(m)) for _ in range(n)]
    O = ocsat.OC(sets, V, m); out = {}
    for Y, o in ocsat.starts(sets, V, m).items():
        b = ocsat.bases_of(Y, n)
        out[tuple(Y)] = {'EXTF': O.holds(b, chain='none'), 'EXT1': O.holds(b, chain='none', A=1),
                         'OC1': O.holds(b, chain='any', A=1), 'RNDF': O.holds(b, chain='any', multi=True),
                         'RND1': O.holds(b, chain='any', A=1, multi=True), 'MD': O.holds(b, md=True)}
    O.close(); return out


def compare(ocsat, V, C, tag=''):
    cc = c_classes(V); ss = sat_classes(ocsat, V); bad = 0
    assert set(cc) == set(ss), (cc.keys(), ss.keys())
    for Y in cc:
        for k in cc[Y]:
            C[(k, cc[Y][k])] += 1
            if cc[Y][k] != ss[Y][k]:
                bad += 1; print('MISMATCH', tag, k, json.dumps(V), Y, 'C', cc[Y][k], 'SAT', ss[Y][k], flush=True)
    C['starts'] += len(cc)
    return bad


def run_sat(T, seed, nmin, nmax, mmin, mmax):
    ocsat = ksens_mods(); rng = random.Random(seed); C = collections.Counter(); bad = 0
    for t in range(T):
        n = rng.randint(nmin, nmax); m = rng.randint(max(mmin, n + 1), mmax)
        kind, V = gen(rng, n, m)
        bad += compare(ocsat, V, C, kind)
    for k in sorted(C, key=str): print(k, C[k])
    print('mismatches', bad)


def run_known():
    ocsat = ksens_mods(); C = collections.Counter(); bad = 0
    for name, V in families.named():
        if len(V[0]) > 10: continue
        b = compare(ocsat, V, C, name); bad += b
        print(name, 'n', len(V), 'm', len(V[0]), 'mismatches', b, flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('mismatches', bad)


if __name__ == '__main__':
    t0 = time.time()
    print('$ python3 kgen/rounds/xcheck.py', *sys.argv[1:], flush=True)
    if sys.argv[1] == 'brute': run_brute(int(sys.argv[2]), int(sys.argv[3]))
    elif sys.argv[1] == 'sat': run_sat(*map(int, sys.argv[2:8]))
    else: run_known()
    print('time %.0f s' % (time.time() - t0))
