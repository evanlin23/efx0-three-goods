"""Traps of the EFX0-preserving local-move graph G* (k4/haxell.md §3.4).

A Haxell-type tree keeps every matched unit matched, so whatever its signature it walks inside the graph whose
vertices are the states satisfying the invariant and whose edges are single local moves.  Here the invariant is
the strongest natural one: a *partial EFX0 allocation* (every agent happy with respect to the allocated bundles; the
unallocated goods form the pool).  G* has every such state as a vertex, and an edge for each generic local move
that keeps the invariant and does not enlarge the pool:
  move  one good (allocated or pooled) to another agent;
  swap  two goods held by different holders (the pool counts as a holder), the pool not growing;
  trade two agents exchange their whole bundles.
A *trap* is a partial EFX0 allocation from which no complete EFX0 allocation can be reached in G*.  A trap state
cannot be augmented by any tree whose collapses are single local moves of these kinds.  A *radius-2 trap* survives
composite moves made of two generic moves (the intermediate state need not be EFX0).

The script enumerates every assignment of the goods to agents or pool ((n+1)^m of them), keeps the partial EFX0 ones,
and runs a reverse breadth-first search from the complete EFX0 allocations.  It reports the number of traps, the
traps with the fewest pooled goods, and whether the serial-dictatorship picks of some order are a trap.

    python3 k4/haxell/ht_gstar.py SRC [NMAX=4] [MMAX=8] [SHOW=3]"""
import sys, os, json, itertools, collections, time
from ht_lib import Inst, happy_vec, bundles, instances, sd


def all_partial_efx0(I):
    S = set()
    for own in itertools.product(range(-1, I.n), repeat=I.m):
        if all(happy_vec(I, own)):
            S.add(own)
    return S


def nbrs(I, own):
    n, m = I.n, I.m
    pool = own.count(-1)
    for g in range(m):
        for b in range(n):
            if b != own[g]:
                o = list(own); o[g] = b; yield tuple(o)
    for g, h in itertools.combinations(range(m), 2):
        if own[g] != own[h]:
            o = list(own); o[g], o[h] = own[h], own[g]
            yield tuple(o)          # pool size unchanged by a swap
    for a, b in itertools.combinations(range(n), 2):
        yield tuple(b if x == a else a if x == b else x for x in own)


def radius2_traps(I, S, T):
    """the traps that remain when composite moves of two generic moves are allowed (the intermediate state need
    not be EFX0): fixpoint of removing every trap that has a radius-2 neighbour in S outside the current trap set"""
    T2 = set(T)
    nb2 = {}
    for s in T:
        out = set()
        for t1 in nbrs(I, s):
            for t2 in nbrs(I, t1):
                if t2 in S and t2.count(-1) <= s.count(-1):
                    out.add(t2)
            if t1 in S and t1.count(-1) <= s.count(-1):
                out.add(t1)
        nb2[s] = out
    changed = True
    while changed:
        changed = False
        for s in list(T2):
            if any(t not in T2 for t in nb2[s]):
                T2.discard(s); changed = True
    return T2


def traps(I):
    S = all_partial_efx0(I)
    complete = [s for s in S if -1 not in s]
    # forward adjacency restricted to S; reverse BFS from complete states
    radj = collections.defaultdict(list)
    for s in S:
        for t in nbrs(I, s):
            if t in S and t.count(-1) <= s.count(-1):
                radj[t].append(s)
    good = set(complete); q = collections.deque(complete)
    while q:
        t = q.popleft()
        for s in radj[t]:
            if s not in good:
                good.add(s); q.append(s)
    T = [s for s in S if s not in good]
    return S, complete, T


def job(item):
    name, sets, vals, m = item
    I = Inst(sets, vals, m, name)
    S, comp, T = traps(I)
    T2 = radius2_traps(I, S, T) if T else set()
    sdtrap = 0; Tset = set(T)
    for o in itertools.permutations(range(I.n)):
        Y = sd(I, list(o))[0]
        own = [-1] * m
        for i, g in enumerate(Y):
            if g is not None:
                own[g] = i
        sdtrap += tuple(own) in Tset
    mp = min((s.count(-1) for s in T), default=None)
    ex = [bundles(I, list(s)) for s in T if s.count(-1) == mp][:2] if T else []
    expool = [[g for g in range(m) if s[g] < 0] for s in T if s.count(-1) == mp][:2] if T else []
    ex2 = [(bundles(I, list(s)), [g for g in range(m) if s[g] < 0]) for s in list(T2)[:2]]
    return name, sets, vals, len(S), len(comp), len(T), len(T2), sdtrap, mp, ex, expool, ex2


if __name__ == '__main__' and os.environ.get('GSTAR_PAR'):
    import multiprocessing as mpc
    args = dict(a.split('=') for a in sys.argv[2:] if '=' in a)
    src = sys.argv[1]; nmax = int(args.get('NMAX', '4')); mmax = int(args.get('MMAX', '8'))
    show = int(args.get('SHOW', '3'))
    print('$ GSTAR_PAR=1 python3 k4/haxell/ht_gstar.py', *sys.argv[1:], flush=True)
    t0 = time.time(); C = collections.Counter(); shown = 0
    items = [it for it in instances(src) if len(it[1]) <= nmax and it[3] <= mmax]
    with mpc.Pool(os.cpu_count()) as pool:
        for (name, sets, vals, nS, nC, nT, nT2, sdtrap, mp, ex, expool, ex2) in pool.imap_unordered(job, items):
            C['instances'] += 1; C['partial EFX0 states'] += nS; C['traps'] += nT; C['radius-2 traps'] += nT2
            C['instances with a trap'] += bool(nT); C['instances with a radius-2 trap'] += bool(nT2)
            C['serial-dictatorship starts that are traps'] += sdtrap
            C['instances without a complete EFX0 allocation'] += (nC == 0)
            if nT:
                C['instances with a trap with %d pooled good(s)' % mp] += 1
                if shown < show:
                    shown += 1
                    print('TRAPS', name, json.dumps((sets, vals)), 'states', nS, 'complete', nC, 'traps', nT,
                          'fewest pooled', mp, 'e.g.', ex, 'pool', expool, flush=True)
            if nT2:
                print('RADIUS-2 TRAP', name, json.dumps((sets, vals)), ex2, flush=True)
    for k in sorted(C, key=str):
        print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
    sys.exit(0)


if __name__ == '__main__':
    args = dict(a.split('=') for a in sys.argv[2:] if '=' in a)
    src = sys.argv[1]; nmax = int(args.get('NMAX', '4')); mmax = int(args.get('MMAX', '8'))
    show = int(args.get('SHOW', '3'))
    print('$ python3 k4/haxell/ht_gstar.py', *sys.argv[1:], flush=True)
    t0 = time.time(); C = collections.Counter(); shown = 0
    for name, sets, vals, m in instances(src):
        n = len(sets)
        if n > nmax or m > mmax:
            continue
        I = Inst(sets, vals, m, name)
        S, comp, T = traps(I)
        C['instances'] += 1; C['partial EFX0 states'] += len(S); C['traps'] += len(T)
        sdtrap = 0
        for o in itertools.permutations(range(n)):
            Y = sd(I, list(o))[0]
            own = [-1] * m
            for i, g in enumerate(Y):
                if g is not None:
                    own[g] = i
            if tuple(own) in set(T):
                sdtrap += 1
        C['instances with a trap'] += bool(T)
        T2 = radius2_traps(I, S, T) if T else set()
        C['radius-2 traps'] += len(T2); C['instances with a radius-2 trap'] += bool(T2)
        if T2:
            print('RADIUS-2 TRAP', name, json.dumps((sets, vals)), [bundles(I, list(s)) for s in list(T2)[:2]],
                  'pool', [[g for g in range(m) if s[g] < 0] for s in list(T2)[:2]], flush=True)
        C['serial-dictatorship starts that are traps'] += sdtrap
        if T:
            mp = min(s.count(-1) for s in T)
            C['instances with a trap with %d pooled good(s)' % mp] += 1
            if shown < show:
                shown += 1
                ex = [s for s in T if s.count(-1) == mp][:2]
                print('TRAPS', name, json.dumps((sets, vals)), 'states', len(S), 'complete', len(comp), 'traps', len(T),
                      'fewest pooled', mp, 'e.g.', [bundles(I, list(s)) for s in ex], 'pool',
                      [[g for g in range(m) if s[g] < 0] for s in ex], flush=True)
    for k in sorted(C, key=str):
        print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
