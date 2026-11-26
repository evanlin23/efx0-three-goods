"""ROUND+ stress tests (kgen/rounds.md §2).  Strictly positive integer values, every agent values every good.

    python3 kgen/rounds/stress.py rand KINDS n mmin mmax T SEED
        KINDS: comma list from families.KINDS or 'all'.  Per instance and every distinct start: EXT1/EXTF (picks extend),
        OC1 (one chain), RND1/RNDF (one round).  Prints FAIL lines (a start with no one-round completion) at once.
    python3 kgen/rounds/stress.py climb n m STEPS ROUNDS SEED [init=KIND|named=NAME] [ties]
        adversarial climb minimizing  (-#starts failing one round, then at the hardest start: the number of EFX
        allocations that witness one round (RND1), then the sum of their margins (rnd.c: the smaller of the EFX slack
        and the best structure's gain slack, each normalized by the agent's total value), then -#starts whose picks do
        not extend with one absorber);
        mutations: one value +-, a swap of two values in a row, a fresh random value; values in [1, 3000];
        without 'ties' every row keeps distinct values.
    python3 kgen/rounds/stress.py named
        the lifted named instances of families.named().

Every FAIL is a claim to be confirmed by a second implementation (bruter.py / ksens ocsat).
"""
import sys, os, json, random, collections, time, zlib
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import rndlib, families
VMAX = int(os.environ.get("VMAX", "3000"))
CLASS = os.environ.get("CLASS", "RND1")
# TWINS="1=3,0=2": after every mutation agent j copies agent i's row exactly (identical valuations, k types)
TWINS = [tuple(map(int, p.split('='))) for p in os.environ.get("TWINS", "").split(',') if p]


# KEPS=k: every agent keeps at most k "real" values (its k largest); every other value is clamped into [1, 5]
# (the eps-lift of an instance with at most k relevant goods per agent)
KEPS = int(os.environ.get("KEPS", "0"))
KCOVER = os.environ.get("KCOVER", "0") == "1"   # with KEPS: every good must be a real (> 5) good of some agent


KCORE = os.environ.get("KCORE", "0") == "1"     # with KEPS: the zero version (values <= 5 -> 0) is a k = 4 core
                                                # (k4/SCOUT.md K4.CORE: 3 or 4 relevant goods, strictly balanced,
                                                # private-good limits, every good relevant; connectivity not imposed)


def is_core(Z):
    n, m = len(Z), len(Z[0])
    R = [[g for g in range(m) if Z[i][g] > 0] for i in range(n)]
    for g in range(m):
        if not any(Z[i][g] > 0 for i in range(n)): return False
    for i in range(n):
        if len(R[i]) not in (3, 4): return False
        vs = sorted((Z[i][g] for g in R[i]), reverse=True)
        if not vs[0] < sum(vs[1:]): return False
        priv = [g for g in R[i] if all(Z[j][g] == 0 for j in range(n) if j != i)]
        if len(R[i]) == 3 and len(priv) > 1: return False
        if len(R[i]) == 4:
            if len(priv) > 2: return False
            if len(priv) == 2:
                sh = [g for g in R[i] if g not in priv]
                if not sum(Z[i][g] for g in priv) < sum(Z[i][g] for g in sh): return False
    return True


def valid(V):
    if KEPS and KCORE:
        return is_core([[x if x > 5 else 0 for x in row] for row in V])
    if KEPS and KCOVER:
        return all(any(row[g] > 5 for row in V) for g in range(len(V[0])))
    return True


def twin(V):
    for i, j in TWINS: V[j] = list(V[i])
    if KEPS:
        for row in V:
            big = sorted(range(len(row)), key=lambda g: -row[g])[:KEPS]
            for g in range(len(row)):
                if g not in big: row[g] = max(1, min(5, row[g]))
                elif row[g] <= 5: row[g] = 6
    return V      # the one-round class under test: RND1 (ROUND+) or RNDX1 (ROUND-X)


def summary(V):
    res, ne = rndlib.analyze(V, margin=CLASS)
    st = []
    for s in res:
        c = s['counts']
        st.append({'picks': s['picks'], 'order': s['order'], 'ext1': c['EXT1'] > 0, 'extf': c['EXTF'] > 0,
                   'oc1': c['OC1'] > 0, 'rnd1': c[CLASS], 'rndf': c['RNDF'] if CLASS == 'RND1' else c['RNDX'],
                   'md': c['MD'], 'msum': s['msum'], 'r1': c['RND1']})
    return st, ne


def report_fail(V, s, tag):
    fp = os.environ.get('FAILS')
    if fp:
        with open(fp, 'a') as f:
            f.write(json.dumps({'class': CLASS, 'tag': tag, 'vals': V, 'picks': list(s['picks']), 'order': list(s['order'])}) + '\n')
    print('FAIL', CLASS, tag, 'vals', json.dumps(V), 'picks', list(s['picks']), 'order', list(s['order']),
          'rnd1', s['rnd1'], 'rndf', s['rndf'], 'md', s['md'], flush=True)


def run_rand(kinds, n, mmin, mmax, T, seed):
    rng = random.Random(seed); C = collections.Counter(); mins = {}
    for t in range(T):
        kind = kinds[t % len(kinds)]; m = rng.randint(mmin, mmax)
        V = families.gen(kind, n, m, rng)
        st, ne = summary(V)
        key = (kind, m)
        C[key + ('inst',)] += 1
        for s in st:
            C[key + ('starts',)] += 1
            if not s['ext1']: C[key + ('need_chain_A1',)] += 1
            if not s['extf']: C[key + ('need_chain_free',)] += 1
            if not s['oc1']: C[key + ('one_chain_fails',)] += 1
            if s['rnd1'] == 0: C[key + ('ROUND_FAILS_A1',)] += 1; report_fail(V, s, kind)
            if s['rndf'] == 0: C[key + ('ROUND_FAILS_free',)] += 1
            if s['rnd1'] != s['rndf'] and (s['rnd1'] == 0) != (s['rndf'] == 0): C[key + ('A1_free_differ',)] += 1
            mins[key] = min(mins.get(key, 10 ** 18), s['rnd1'])
    tot = collections.Counter()
    for k in sorted(C, key=str):
        print(*k, C[k]); tot[k[2]] += C[k]
    for k in sorted(mins, key=str): print('min RND1 witnesses', *k, mins[k])
    print('TOTAL', dict(tot))


def objective(V):
    st, ne = summary(V)
    fails = sum(1 for s in st if s['rnd1'] == 0)
    h = min(st, key=lambda s: (s['rnd1'], s['msum']))
    hard = sum(1 for s in st if not s['ext1'])
    return (-fails, h['rnd1'], round(h['msum'], 9), -hard), st


def run_climb(n, m, steps, rounds, seed, init, ties):
    rng = random.Random(seed); t0 = time.time()
    named = dict(families.named())
    for r in range(rounds):
        if init.startswith('named='):
            V = [list(x) for x in named[init[6:]]]
        else:
            V = families.gen(init, n, m, rng)
            if not ties:
                V = [rng.sample(range(1, 3000), m) if len(set(row)) < m else row for row in V]
        n_, m_ = len(V), len(V[0])
        V = twin(V); tries = 0
        while not valid(V) and tries < 20000 and not init.startswith('named='):
            V = twin(families.gen(init, n, m, rng)); tries += 1
        c, st = objective(V)
        for s in range(steps):
            V2 = [list(x) for x in V]; i = rng.randrange(n_); g = rng.randrange(m_); u = rng.random()
            if u < 0.6:
                V2[i][g] = max(1, min(VMAX, V2[i][g] + rng.choice([-50, -20, -9, -5, -3, -1, 1, 3, 5, 9, 20, 50])))
            elif u < 0.85:
                h = rng.randrange(m_); V2[i][g], V2[i][h] = V2[i][h], V2[i][g]
            elif u < 0.95:
                V2[i][g] = rng.randint(1, VMAX)
            else:   # copy a row (pushes toward identical agents) with a small perturbation
                j = rng.randrange(n_); V2[i] = [max(1, x + rng.randint(-2, 2)) for x in V2[j]]
            if not ties and len(set(V2[i])) < m_: continue
            V2 = twin(V2)
            if not valid(V2): continue
            c2, st2 = objective(V2)
            if c2 <= c:
                V, c, st = V2, c2, st2
                if c[0] < 0:
                    for x in st:
                        if x['rnd1'] == 0: report_fail(V, x, 'climb')
                    break
        hardest = min(st, key=lambda x: (x['rnd1'], x['msum']))
        print('round', r, 'final', c, 'hardest', list(hardest['picks']), 'order', list(hardest['order']),
              'vals', json.dumps(V), 'time %.0f' % (time.time() - t0), flush=True)


def run_named():
    for name, V in families.named():
        st, ne = summary(V)
        print(name, 'n', len(V), 'm', len(V[0]), 'EFX allocations', ne, 'starts', len(st),
              'need chain (A1)', sum(1 for s in st if not s['ext1']), 'one chain fails', sum(1 for s in st if not s['oc1']),
              'one round fails', sum(1 for s in st if s['rnd1'] == 0), 'min RND1', min(s['rnd1'] for s in st), flush=True)
        for s in st:
            if s['rnd1'] == 0: report_fail(V, s, name)


if __name__ == '__main__':
    t0 = time.time()
    print('$ python3 kgen/rounds/stress.py', *sys.argv[1:], flush=True)
    mode = sys.argv[1]
    if mode == 'rand':
        kinds = families.KINDS if sys.argv[2] == 'all' else sys.argv[2].split(',')
        run_rand(kinds, *map(int, sys.argv[3:8]))
    elif mode == 'climb':
        n, m, steps, rounds = map(int, sys.argv[2:6])
        seed = int(sys.argv[6]) if sys.argv[6].isdigit() else zlib.crc32(sys.argv[6].encode())
        init = next((a for a in sys.argv[7:] if a != 'ties'), 'generic')
        run_climb(n, m, steps, rounds, seed, init, 'ties' in sys.argv[7:])
    else:
        run_named()
    print('time %.0f s' % (time.time() - t0))
