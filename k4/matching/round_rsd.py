"""ROUND-RSD (the coordinator's proposal; k4/matching.md §6): iterated reduction in which a step is a *round* of
simultaneous settlements.

One round at a perfect SD start B of the current instance I' (present agents, present goods):
  - choose r >= 1 settlements (k_a, P_a, T_a), up to RMAX of them.  P_a is a canonical chain from an agent k_a that is
    dangerous in I' at B, and T_a, inside (J' + B_end(a)) and R_{k_a}, is improving for k_a.  The chains must be
    pairwise vertex-disjoint and the T_a pairwise disjoint;
  - apply them all at once;
  - (L*) at the end of the round: no T_a threatens any other agent that was present at the round's start, at its
    value after the round.  The other settled agents of the round count, at v(T_b).  LSTAR=defer drops this, and
    only the final raw test remains;
  - delete every k_a and T_a; the rest must be a perfect SD outcome of the smaller instance.
The search recurses up to DMAX rounds and ends in a one-absorber completion at once that lifts (rsd.lifted_completion:
deleted agents keep T and receive nothing, the owner is present, raw EFX0 in I).  RMAX = 1 is RSD.

For each start it records the least number of rounds, the round sizes and the T sizes.  With RSD_WIT it writes
witnesses (each round: its settlements and the full state after it) for check_rsd.py.

With ROUNDS=scc a round is instead a strongly connected component of the coordinator's threat graph on the
candidate settlements, of any size: an arc s -> s' when s's T threatens an agent off s's chain that lies on s''s
chain.  The members must be pairwise compatible, and (L*) is still checked at the round's end.  Two sharper forms:
ROUNDS=minimal takes singletons, plus the pairs neither of whose members passes (L*) alone; ROUNDS=scc2 takes
singletons, plus the 2-cycles of the threat graph.  With EXPLORE=1 the
script also walks every sequence of admissible rounds and reports whether a dead end is reachable.  With
KNOWN_HARD=1 the root completion test is skipped, for inputs already certified hard.  This can only lose a
zero-round repair, never accept a wrong witness, since check_rsd.py re-checks every witness.

    [RMAX=2] [DMAX=4] [LSTAR=now|defer] [ROUNDS=all|scc] [EXPLORE=1] [RSD_WIT=out.json.gz]
    python3 k4/matching/round_rsd.py INPUT [INPUT ...]"""
import sys, os, json, gzip, itertools, collections, time, multiprocessing as mp
import _mpaths  # noqa: F401
from mlib import M
from n5_census import load
from rsd import sub_instance, lifted_completion

RMAX = int(os.environ.get('RMAX', '2')); DMAX = int(os.environ.get('DMAX', '4'))
LSTAR = os.environ.get('LSTAR', 'now')
ROUNDS = os.environ.get('ROUNDS', 'all')   # 'all': any compatible set of <= RMAX settlements; 'scc': strongly connected
                                           # components of the threat graph (the coordinator's variant), any size;
                                           # 'minimal': singletons and pairs needed together; 'scc2': singletons and
                                           # 2-cycles of the threat graph


def settlements(Im, Bm):
    """(km, P, T) for every canonical chain from a dangerous agent of Im and every improving T in its pool."""
    Jm = Im.junk(Bm); out = []
    for km in Im.dangerous(Bm):
        chains = []

        def ext(path):
            for w in range(Im.n):
                if w in path or not Im.wants(w, Bm[path[-1]][0], Bm): continue
                chains.append(tuple(path + [w])); ext(path + [w])
        ext([km])
        for P in chains:
            pool = [g for g in Jm + list(Bm[P[-1]]) if g in Im.R[km]]
            for r in range(1, len(pool) + 1):
                for T in itertools.combinations(pool, r):
                    if Im.V(km, T) > Im.V(km, Bm[km]): out.append((km, P, T))
    return out


def scc_rounds(Im, Bm, S):
    """The coordinator's threat graph on the settlements S: an arc s -> s' when s's T threatens (at current values) an
    agent off s's chain that lies on s''s chain.  Yields every strongly connected component whose members are
    pairwise compatible (vertex-disjoint chains, disjoint T)."""
    n = len(S); adj = [[] for _ in range(n)]
    for a, (k, P, T) in enumerate(S):
        thr = [i for i in range(Im.n) if i not in P and Im.threat(i, list(T), Im.V(i, Bm[i]))]
        for b, (k2, P2, T2) in enumerate(S):
            if b != a and any(i in P2 for i in thr): adj[a].append(b)
    idx = {}; low = {}; st = []; on = set(); comps = []; cnt = [0]

    def strong(v):
        idx[v] = low[v] = cnt[0]; cnt[0] += 1; st.append(v); on.add(v)
        for w in adj[v]:
            if w not in idx: strong(w); low[v] = min(low[v], low[w])
            elif w in on: low[v] = min(low[v], idx[w])
        if low[v] == idx[v]:
            c = []
            while True:
                w = st.pop(); on.discard(w); c.append(w)
                if w == v: break
            comps.append(c)
    sys.setrecursionlimit(10000)
    for v in range(n):
        if v not in idx: strong(v)
    for c in comps:
        combo = [S[v] for v in c]
        agents = [x for _, P, _ in combo for x in P]; Ts = [g for _, _, T in combo for g in T]
        if len(agents) == len(set(agents)) and len(Ts) == len(set(Ts)): yield combo


def rounds(I, alive, goods, B):
    """Yield (settled list [(k, T, P)], new full state) for every admissible round."""
    Im, g2 = sub_instance(I, alive, goods); inv = {t: g for g, t in g2.items()}
    Bm = [[g2[g] for g in B[i]] for i in alive]
    S = settlements(Im, Bm)
    def lstar_ok(combo):
        nb = [list(b) for b in Bm]
        for km, P, T in combo:
            nb[km] = list(T)
            for t in range(1, len(P)): nb[P[t]] = list(Bm[P[t - 1]])
        return not any(Im.threat(i, list(T), Im.V(i, nb[i])) for km, _, T in combo for i in range(Im.n) if i != km)

    def threatens(s, s2):   # the coordinator's arc s -> s2
        k, P, T = s
        return any(i not in P and i in s2[1] and Im.threat(i, list(T), Im.V(i, Bm[i])) for i in range(Im.n))
    if ROUNDS == 'scc':
        combos = scc_rounds(Im, Bm, S)
    elif ROUNDS == 'minimal':   # singletons, and pairs neither of whose members passes (L*) alone
        alone = {s: lstar_ok([s]) for s in S}
        combos = itertools.chain(((s,) for s in S),
                                 (c for c in itertools.combinations(S, 2) if not alone[c[0]] and not alone[c[1]]))
    elif ROUNDS == 'scc2':      # singletons, and 2-cycles of the threat graph
        combos = itertools.chain(((s,) for s in S),
                                 (c for c in itertools.combinations(S, 2) if threatens(c[0], c[1]) and threatens(c[1], c[0])))
    else:
        combos = (c for r in range(1, RMAX + 1) for c in itertools.combinations(S, r))
    for combo in combos:
        if True:
            agents = [x for _, P, _ in combo for x in P]
            if len(agents) != len(set(agents)): continue
            Ts = [g for _, _, T in combo for g in T]
            if len(Ts) != len(set(Ts)): continue
            # a released end good used by another settlement's T is impossible: each T only uses junk + its own end's good
            nb = [list(b) for b in Bm]
            for km, P, T in combo:
                nb[km] = list(T)
                for t in range(1, len(P)): nb[P[t]] = list(Bm[P[t - 1]])
            ks = [km for km, _, _ in combo]
            if LSTAR != 'defer':
                if any(Im.threat(i, list(T), Im.V(i, nb[i])) for km, _, T in combo for i in range(Im.n) if i != km): continue
            full = [list(b) for b in B]
            for a, i in enumerate(alive): full[i] = [inv[g] for g in nb[a]]
            K = [alive[km] for km in ks]; Tall = set(inv[g] for g in Ts)
            alive2 = [a for a in alive if a not in K]; goods2 = [g for g in goods if g not in Tall]
            if any(len(full[i]) != 1 for i in alive2): continue
            if alive2:
                I2, h2 = sub_instance(I, alive2, goods2)
                Y2 = tuple(h2[full[i][0]] for i in alive2)
                if not any(I2.sd(p) == Y2 for p in itertools.permutations(range(I2.n))): continue
            yield [(alive[km], [inv[g] for g in T], [alive[p] for p in P]) for km, P, T in combo], full


def search(I, alive, goods, B, dead, d, memo=None):
    """memo caches, per state, the lifted completion and the admissible rounds across the iterative deepening."""
    memo = {} if memo is None else memo
    key = (tuple(alive), json.dumps(B))
    if key not in memo:
        X = lifted_completion(I, B, dead) if alive else (B if I.efx0(B) else None)
        memo[key] = [X, None]
    X = memo[key][0]
    if X is not None: return [('X', X)]
    if d == 0: return None
    if memo[key][1] is None: memo[key][1] = list(rounds(I, alive, goods, B))
    for settled, full in memo[key][1]:
        K = [k for k, _, _ in settled]; Tall = set(g for _, T, _ in settled for g in T)
        r = search(I, [a for a in alive if a not in K], [g for g in goods if g not in Tall], full, dead | set(K), d - 1, memo)
        if r is not None: return [(settled, full)] + r
    return None


def explore(I, alive, goods, B, dead, d, memo, C):
    """Every state reachable by admissible rounds (at most d more): False if a dead end (no lifting completion, no
    admissible round) is reachable."""
    key = (tuple(alive), json.dumps(B))
    if key in memo: return memo[key]
    X = lifted_completion(I, B, dead) if alive else (B if I.efx0(B) else None)
    nxt = list(rounds(I, alive, goods, B)) if d > 0 and X is None else []
    if X is None and not nxt:
        C['dead-end states reachable%s' % ('' if d > 0 else ' (depth limit)')] += 1; memo[key] = False; return False
    ok = True
    for settled, full in nxt:
        K = [k for k, _, _ in settled]; Tall = set(g for _, T, _ in settled for g in T)
        ok &= explore(I, [a for a in alive if a not in K], [g for g in goods if g not in Tall], full, dead | set(K), d - 1,
                      memo, C)
    memo[key] = ok; return ok


def job(row):
    I = M(row['sets'], row['vals']); B = [[g] for g in row['picks']]; C = collections.Counter(); wit = None
    found = None; memo = {}
    if row.get('known_hard') or os.environ.get('KNOWN_HARD') == '1':   # the input already certifies that the start has no completion (skip the root test)
        memo[(tuple(range(I.n)), json.dumps(B))] = [None, None]
    for d in range(DMAX + 1):
        r = search(I, list(range(I.n)), list(range(I.m)), B, frozenset(), d, memo)
        if r is not None: found = (d, r); break
    if found is None:
        C['ROUND-RSD: none with <= %d rounds' % DMAX] += 1
        sys.stdout.write('ROUND-RSD FAILS %s\n' % json.dumps({'sets': row['sets'], 'vals': row['vals'], 'picks': list(row['picks'])}))
        sys.stdout.flush()
    else:
        d, r = found; rs = r[:-1]
        assert I.efx0(r[-1][-1])
        C['ROUND-RSD: least number of rounds = %d' % d] += 1
        C['ROUND-RSD: round sizes %s' % [len(s) for s, _ in rs]] += 1
        C['ROUND-RSD: T sizes %s' % [[len(T) for _, T, _ in s] for s, _ in rs]] += 1
        wit = {'k': row.get('_k'), 'rounds': [{'settled': [{'k': k, 'T': T, 'P': P} for k, T, P in s], 'state': full}
                                             for s, full in rs], 'alloc': r[-1][-1]}
    if os.environ.get('EXPLORE'):
        D = collections.Counter()
        ok = explore(I, list(range(I.n)), list(range(I.m)), B, frozenset(), DMAX, {}, D)
        C['EXPLORE: no dead end reachable %s' % ok] += 1
    return C, wit


if __name__ == '__main__':
    rows = []
    for a in sys.argv[1:]: rows += load(a)
    seen = set(); R = []
    for r in rows:
        key = json.dumps([r['sets'], r['vals'], list(r['picks'])])
        if key not in seen: seen.add(key); R.append(r)
    for t, r in enumerate(R): r['_k'] = t
    print('$ RMAX=%d DMAX=%d LSTAR=%s ROUNDS=%s EXPLORE=%s python3 k4/matching/round_rsd.py' % (RMAX, DMAX, LSTAR, ROUNDS, os.environ.get('EXPLORE', '')), *sys.argv[1:], '|',
          len(R), 'distinct starts', flush=True)
    T = collections.Counter(); t0 = time.time(); WIT = []
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for t, (C, wit) in enumerate(pool.imap_unordered(job, R, chunksize=4 if len(R) > 1000 else 1)):
            T.update(C)
            if wit is not None: WIT.append(wit)
            if (t + 1) % 10000 == 0: print('...', t + 1, '%.0f s' % (time.time() - t0), flush=True)
    for k in sorted(T): print(k, T[k])
    if os.environ.get('RSD_WIT'):
        WIT.sort(key=lambda w: w['k'])
        with gzip.open(os.environ['RSD_WIT'], 'wt') as f:
            json.dump({'what': 'ROUND-RSD witnesses (k4/matching/round_rsd.py, RMAX=%d LSTAR=%s): per start k (index into the '
                               'distinct input rows), the rounds (settled agents with T and chain P, full state after the '
                               'round) and the final allocation' % (RMAX, LSTAR), 'inputs': sys.argv[1:], 'witnesses': WIT}, f)
        print('wrote', os.environ['RSD_WIT'], len(WIT), 'witnesses')
    print('time %.0f s' % (time.time() - t0))
