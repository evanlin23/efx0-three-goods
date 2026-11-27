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

    [RMAX=2] [DMAX=4] [LSTAR=now|defer] [RSD_WIT=out.json.gz] python3 k4/matching/round_rsd.py INPUT [INPUT ...]"""
import sys, os, json, gzip, itertools, collections, time, multiprocessing as mp
import _mpaths  # noqa: F401
from mlib import M
from n5_census import load
from rsd import sub_instance, lifted_completion

RMAX = int(os.environ.get('RMAX', '2')); DMAX = int(os.environ.get('DMAX', '4'))
LSTAR = os.environ.get('LSTAR', 'now')


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


def rounds(I, alive, goods, B):
    """Yield (settled list [(k, T, P)], new full state) for every admissible round."""
    Im, g2 = sub_instance(I, alive, goods); inv = {t: g for g, t in g2.items()}
    Bm = [[g2[g] for g in B[i]] for i in alive]
    S = settlements(Im, Bm)
    for r in range(1, RMAX + 1):
        for combo in itertools.combinations(S, r):
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


def search(I, alive, goods, B, dead, d):
    X = lifted_completion(I, B, dead) if alive else (B if I.efx0(B) else None)
    if X is not None: return [('X', X)]
    if d == 0: return None
    for settled, full in rounds(I, alive, goods, B):
        K = [k for k, _, _ in settled]; Tall = set(g for _, T, _ in settled for g in T)
        r = search(I, [a for a in alive if a not in K], [g for g in goods if g not in Tall], full, dead | set(K), d - 1)
        if r is not None: return [(settled, full)] + r
    return None


def job(row):
    I = M(row['sets'], row['vals']); B = [[g] for g in row['picks']]; C = collections.Counter(); wit = None
    found = None
    for d in range(DMAX + 1):
        r = search(I, list(range(I.n)), list(range(I.m)), B, frozenset(), d)
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
    return C, wit


if __name__ == '__main__':
    rows = []
    for a in sys.argv[1:]: rows += load(a)
    seen = set(); R = []
    for r in rows:
        key = json.dumps([r['sets'], r['vals'], list(r['picks'])])
        if key not in seen: seen.add(key); R.append(r)
    for t, r in enumerate(R): r['_k'] = t
    print('$ RMAX=%d DMAX=%d LSTAR=%s python3 k4/matching/round_rsd.py' % (RMAX, DMAX, LSTAR), *sys.argv[1:], '|',
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
