"""Counterexample hunt for Conjecture RF at k = 4 through twins (the coordinator's request; K4.SDC.RF, K4.SDC.RF.K5EVERY).

At k = 5 the every-order form of RF fails through two identical agents: the receiver-first order only swaps the twins'
picks (k4/sdc/rf_k5_twin_cex.py).  Here, strict connected k = 4 cores (oc1max_climb.is_core) with a twin pair (two
agents with identical sets and values) are searched at n = 5, 6.  At every maximum-matching SD start where OC1 fails
(raw: k4/sdc/oc1_mc2_rand.Inst.check), and for every receiver u (an agent whose pick no other agent prefers to its own),
over the u-first orders whose picks are a maximum matching, the hunt tests:
  (a) the every-form: all of them satisfy OC1;
  (b) RF-exists for u: some of them satisfies OC1.  "(b) for some receiver" is also recorded.
Sources:
  rand  random cores (oc1_mc2_rand.gen at n - 1) with one agent duplicated;
  dup4  the 11 OC1^max-failing n = 4 cores (every stored failing profile) with one agent duplicated, giving n = 5;
  dup5  the 280 stored n = 5 failing starts of compute/k4-oc1max-cert's chunk 5_pure_s5o0 with one agent duplicated,
        giving n = 6;
  rf5   ksens's RF5 (k = 5, n = 4, twins 2 and 3) with agents 0 and 1 shrunk to 4 goods (every choice) and one or two
        random agents added (n = 5, 6);
  twin5 the stored n = 5 failing starts whose two agents share a set, with the values made identical;
  twin6 twin5 plus one random agent (n = 6);
  climb hill-climb on values from the failing seeds, mutating both twins identically (climbtwin5 / climbtwin6 start
        from twin5 / twin6).  The score is
        10000 * (b fails) + 1000 * (a fails) + 50 * (twin-swap preconditions: a twin receiver whose twin holds their top
        good) + 5 * (failing starts with a twin receiver) + (OC1^max-failing starts).
  soft  softtwin6 / softrand6 / softrand5: a twin-preserving climb on values and sets, scored by the coordinator's
        OC1^max climb score (k4/sdc/oc1max_climb.evaluate: failures, starts needing a move, danger) plus the RF
        bonus above.  It is meant to reach the failure region from random twin cores.
  twintop5 / twintop6: at every maximum-matching start of the twin5 / twin6 instances with a twin receiver whose twin
        holds their common top good, the OC1 status (Conjecture TWIN-TOP: OC1 never fails there).
Every (a) or (b) failure is printed as JSON.

    python3 k4/matching/twin_hunt.py SOURCE [COUNT] [SEED]"""
import sys, os, json, gzip, random, itertools, collections, time, multiprocessing as mp
import _mpaths  # noqa: F401
from oc1_mc2_rand import Inst, gen
from oc1_max_orders import nu
from oc1max_climb import is_core

ROOT = _mpaths.ROOT


def receivers(I, P):
    return [u for u in range(I.n) if P[u] is not None and
            all(I.v[i].get(P[u], 0) <= I.v[i].get(P[i], 0) for i in range(I.n) if i != u)]


def evaluate(sets, vals):
    """(counter, failures) over every OC1^max-failing start of the instance."""
    I = Inst(sets, vals); n = I.n; N = nu(I); C = collections.Counter(); fails = []
    starts = {}
    for o in itertools.permutations(range(n)):
        p = I.sd(o)
        if sum(x is not None for x in p) == N: starts.setdefault(p, o)
    checked = {}

    def chk(p):
        if p not in checked: checked[p] = I.check(p)
        return checked[p]
    for P in starts:
        if chk(P) != 'OC1 fails': continue
        C['OC1max-failing starts'] += 1
        rec = receivers(I, P); C['receivers = %d' % len(rec)] += 1
        some_any = False
        for u in rec:
            vecs = set()
            for rest in itertools.permutations([i for i in range(n) if i != u]):
                p = I.sd((u,) + rest)
                if sum(x is not None for x in p) == N: vecs.add(p)
            res = {p: chk(p) != 'OC1 fails' for p in vecs}
            a_ok = all(res.values()) and bool(res); b_ok = any(res.values())
            some_any |= b_ok
            C['(a) every-form holds %s' % a_ok] += 1; C['(b) RF-exists for u holds %s' % b_ok] += 1
            if not res: C['receiver with no u-first maximum-matching order'] += 1
            if not a_ok or not b_ok:
                fails.append({'kind': 'b' if not b_ok else 'a', 'sets': sets, 'vals': vals, 'start': list(P), 'u': u,
                              'u_first': {json.dumps(list(p)): ok for p, ok in res.items()}})
        C['(b) RF-exists for some receiver holds %s' % some_any] += 1
        tw = twins(sets, vals); tagents = set(x for pr in tw for x in pr)
        for u in rec:   # the twin-swap precondition: u is a twin and its twin holds their common favourite good
            if u in tagents:
                C['failing start with a twin receiver'] += 1
                t = [b if a == u else a for a, b in tw if u in (a, b)][0]
                if P[t] == max(I.v[u], key=lambda g: I.v[u][g]): C['... and the other twin holds the top good'] += 1
        if not some_any and rec:
            fails.append({'kind': 'b-all', 'sets': sets, 'vals': vals, 'start': list(P)})
    return C, fails


def score(C):
    return (10000 * C['(b) RF-exists for u holds False'] + 1000 * C['(a) every-form holds False'] +
            50 * C['... and the other twin holds the top good'] + 5 * C['failing start with a twin receiver'] +
            C['OC1max-failing starts'])


def dup(sets, vals, a):
    return [list(s) for s in sets] + [list(sets[a])], [list(x) for x in vals] + [list(vals[a])]


def seeds_dup4():
    d = json.load(gzip.open(os.path.join(ROOT, 'results', 'k4_matching', 'data', 'two_move_starts_n4.json.gz'), 'rt'))
    out = []; seen = set()
    for hg in d['hypergraphs']:
        for st in hg['starts'][::40]:
            for a in range(len(hg['sets'])):
                s, v = dup(hg['sets'], st['vals'], a); k = json.dumps([s, v])
                if k not in seen: seen.add(k); out.append((s, v))
    return out


def seeds_dup5():
    out = []; seen = set()
    for l in gzip.open(os.path.join(ROOT, 'results', 'k4_matching', 'data', 'n5_5pure_s5o0_two_move_starts.jsonl.gz'), 'rt'):
        r = json.loads(l)
        for a in range(len(r['sets'])):
            s, v = dup(r['sets'], r['vals'], a); k = json.dumps([s, v])
            if k not in seen: seen.add(k); out.append((s, v))
    return out


def seeds_twin5():
    """The stored n = 5 failing starts in which two agents have the same set (same order of goods): make their
    values identical (either way round)."""
    out = []; seen = set()
    for l in gzip.open(os.path.join(ROOT, 'results', 'k4_matching', 'data', 'n5_5pure_s5o0_two_move_starts.jsonl.gz'), 'rt'):
        r = json.loads(l); S = r['sets']
        for a in range(len(S)):
            for b in range(len(S)):
                if a != b and S[a] == S[b]:
                    v = [list(x) for x in r['vals']]; v[b] = list(v[a]); k = json.dumps([S, v])
                    if k not in seen and is_core(S, v, False): seen.add(k); out.append((S, v))
    return out


def seeds_twin6(rng, count):
    """twin5 instances plus one random agent (3 or 4 goods among the existing ones and at most one new good)."""
    base = seeds_twin5(); out = []
    for _ in range(count * 100):
        if len(out) >= count: break
        S, V = rng.choice(base); m = 1 + max(max(x) for x in S)
        size = rng.choice([3, 4]); s = sorted(rng.sample(range(m + 1), size))
        sets = [list(x) for x in S] + [s]; vals = [list(x) for x in V] + [[rng.randint(1, 40) for _ in s]]
        goods = sorted(set(g for x in sets for g in x)); ren = {g: t for t, g in enumerate(goods)}
        sets = [[ren[g] for g in x] for x in sets]
        if is_core(sets, vals, False): out.append((sets, vals))
    return out


RF5_SETS = [[0, 1, 2, 5, 6], [1, 2, 4, 5, 6], [3, 4, 5, 6], [3, 4, 5, 6]]
RF5_VALS = [[3, 35, 33, 43, 39], [20, 26, 16, 43, 32], [8, 2, 7, 4], [8, 2, 7, 4]]


def seeds_rf5(rng, count):
    out = []
    for _ in range(count * 50):
        if len(out) >= count: break
        sets = [list(s) for s in RF5_SETS]; vals = [list(x) for x in RF5_VALS]
        for a in (0, 1):
            k = rng.randrange(5); del sets[a][k]; del vals[a][k]
        extra = rng.choice([1, 2]); m = 1 + max(max(s) for s in sets)
        for _ in range(extra):
            size = rng.choice([3, 4]); pool = list(range(m + 1))
            s = sorted(rng.sample(pool, size)); m = max(m, max(s) + 1)
            sets.append(s); vals.append([rng.randint(1, 40) for _ in s])
        goods = sorted(set(g for s in sets for g in s)); ren = {g: t for t, g in enumerate(goods)}
        sets = [[ren[g] for g in s] for s in sets]
        if is_core(sets, vals, False): out.append((sets, vals))
    return out


def seeds_rand(rng, count, n):
    out = []
    while len(out) < count:
        try:
            s, v = gen(n - 1, rng)
        except ValueError:   # gen's random good count can be too small for the chosen degrees; draw again
            continue
        a = rng.randrange(n - 1); s, v = dup(s, v, a)
        if is_core(s, v, False): out.append((s, v))
    return out


def twins(sets, vals):
    return [(i, j) for i in range(len(sets)) for j in range(i + 1, len(sets)) if sets[i] == sets[j] and vals[i] == vals[j]]


def climb(args):
    sets, vals, steps, seed = args
    rng = random.Random(seed); C, fails = evaluate(sets, vals); best = score(C); found = list(fails); T = collections.Counter(C)
    tw = twins(sets, vals)
    for _ in range(steps):
        v2 = [list(x) for x in vals]; i = rng.randrange(len(v2)); k = rng.randrange(len(v2[i]))
        v2[i][k] = max(1, v2[i][k] + rng.choice([-3, -2, -1, 1, 2, 3]))
        for a, b in tw:   # keep the twins identical
            if i == a: v2[b] = list(v2[a])
            if i == b: v2[a] = list(v2[b])
        if not is_core(sets, v2, False) or not twins(sets, v2): continue
        C, fails = evaluate(sets, v2); T['profiles'] += 1; T.update(C); found += fails
        sc = score(C)
        if sc >= best: vals, best = v2, sc
    return T, found


def softclimb(args):
    """Twin-preserving climb with the coordinator's OC1^max climb score (oc1max_climb.evaluate: failures, starts that
    need a move, danger) plus this hunt's RF bonus; set mutations of a twin are mirrored on its twin."""
    from oc1max_climb import evaluate as ocev, mutate
    sets, vals, steps, seed = args
    rng = random.Random(seed); T = collections.Counter(); found = []
    tw = twins(sets, vals)
    if not tw: return T, found

    def total(s, v):
        sc, fl = ocev(s, v)
        if fl:
            C, fails = evaluate(s, v); T.update(C); found.extend(fails); sc += score(C)
        return sc
    best = total(sets, vals)
    for _ in range(steps):
        r = mutate(sets, vals, rng)
        if r is None: continue
        s2, v2 = r
        a, b = tw[0]
        # mirror the twin: whichever of the pair changed, copy it onto the other
        if s2[a] != sets[a] or v2[a] != vals[a]: s2[b], v2[b] = list(s2[a]), list(v2[a])
        elif s2[b] != sets[b] or v2[b] != vals[b]: s2[a], v2[a] = list(s2[b]), list(v2[b])
        used = sorted(set().union(*map(set, s2))); ren = {g: t for t, g in enumerate(used)}
        s2 = [[ren[g] for g in x] for x in s2]
        if not is_core(s2, v2, False) or (a, b) not in twins(s2, v2): continue
        T['profiles'] += 1
        sc = total(s2, v2)
        if sc >= best: sets, vals, best = s2, v2, sc
    T['final best score %d' % (best // 1000)] += 1
    return T, found


def job(sv):
    return evaluate(*sv)


def twintop(sv):
    """Every maximum-matching start of the instance with a twin receiver u whose twin holds their common top good:
    the OC1 status (raw Inst.check) of each (Conjecture TWIN-TOP: it is never 'OC1 fails')."""
    sets, vals = sv; I = Inst(sets, vals); N = nu(I); tw = twins(sets, vals); ta = set(x for pr in tw for x in pr)
    C = collections.Counter(); starts = set()
    for o in itertools.permutations(range(I.n)):
        p = I.sd(o)
        if sum(x is not None for x in p) == N: starts.add(p)
    for P in starts:
        for u in receivers(I, P):
            if u not in ta: continue
            t = [b if a == u else a for a, b in tw if u in (a, b)][0]
            if P[t] == max(I.v[u], key=lambda g: I.v[u][g]):
                C['twin-top configuration: ' + I.check(P)] += 1
    return C, []


if __name__ == '__main__':
    src = sys.argv[1]; COUNT = int(sys.argv[2]) if len(sys.argv) > 2 else 200; SEED = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    rng = random.Random(SEED); print('$ python3 k4/matching/twin_hunt.py', *sys.argv[1:], flush=True)
    if src == 'twin5': S = seeds_twin5()
    elif src == 'twin6': S = seeds_twin6(rng, COUNT)
    elif src == 'climbtwin5': S = seeds_twin5()
    elif src == 'climbtwin6': S = seeds_twin6(rng, COUNT)
    elif src == 'softtwin6': S = seeds_twin6(rng, COUNT)
    elif src == 'twintop5': S = seeds_twin5()
    elif src == 'twintop6': S = seeds_twin6(rng, COUNT)
    elif src == 'softrand6': S = seeds_rand(rng, COUNT, 6)
    elif src == 'softrand5': S = seeds_rand(rng, COUNT, 5)
    elif src == 'dup4': S = seeds_dup4()
    elif src == 'dup5': S = seeds_dup5()
    elif src == 'rf5': S = seeds_rf5(rng, COUNT)
    elif src.startswith('rand'): S = seeds_rand(rng, COUNT, int(src[4:] or 5))
    elif src.startswith('climb'):   # climbN: climb from the dup4 (n = 5) or dup5 (n = 6) seeds that have failing starts
        base = seeds_dup4() if src == 'climb5' else seeds_dup5()
        rng.shuffle(base); S = base[:COUNT]
    else: raise SystemExit('unknown source')
    S = [(s, v) for s, v in S if is_core(s, v, False)]
    print('instances', len(S), flush=True)
    T = collections.Counter(); t0 = time.time(); F = []
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        if src.startswith('twintop'):
            it = pool.imap_unordered(twintop, S, chunksize=2)
        elif src.startswith('soft'):
            it = pool.imap_unordered(softclimb, [(s, v, int(os.environ.get('STEPS', '300')), SEED * 7919 + t) for t, (s, v) in enumerate(S)])
        elif src.startswith('climb'):
            it = pool.imap_unordered(climb, [(s, v, int(os.environ.get('STEPS', '300')), SEED * 7919 + t) for t, (s, v) in enumerate(S)])
        else:
            it = pool.imap_unordered(job, S, chunksize=2)
        for t, (C, fails) in enumerate(it):
            T.update(C); F += fails
            for f in fails: print('FAIL', json.dumps(f), flush=True)
            if (t + 1) % 200 == 0: print('...', t + 1, '%.0f s' % (time.time() - t0), flush=True)
    for k in sorted(T): print(k, T[k])
    print('failures: (a) %d, (b) %d, (b) for every receiver %d' % (sum(f['kind'] == 'a' for f in F), sum(f['kind'] == 'b' for f in F),
                                                                 sum(f['kind'] == 'b-all' for f in F)))
    print('time %.0f s' % (time.time() - t0))
