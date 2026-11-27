"""Batch runner for kcegar.py (k4/ksens.md §8): OC_D^max for every strict profile of every hypergraph in a list.

    python3 k4/ksens/kcegar_batch.py genbg n k D [m ...] [--jobs=4] [--limit=SEC]    every connected hypergraph with n
                                                                                      agents, each valuing <= k goods
    python3 k4/ksens/kcegar_batch.py named D [--jobs=4] [--limit=SEC]                 the k = 5 list NAMED below
    python3 k4/ksens/kcegar_batch.py core5 n D [m ...] [--jobs=4] [--limit=SEC]         the k = 5 core-like class: connected,
                                                     agent degrees 3-5 with at least one 5, at most d - 2 private goods
                                                     per agent of degree d (an analogue of the k = 4 cores of
                                                     k4/search4.py; no reduction lemma behind it at k = 5)
    python3 k4/ksens/kcegar_batch.py named6 D [--jobs=4] [--limit=SEC]                designed k = 6 hypergraphs (NAMED6 below)
    python3 k4/ksens/kcegar_batch.py core n K D [m ...] [--jobs=4] [--limit=SEC]       the core-like class of core5 with K
                                                     in place of 5 (agent degrees 3-K with at least one K)
--any-start: every SD start, not only the maximum-matching ones (the official move rule either way).
--kmin=K: (genbg) only hypergraphs in which some agent values at least K goods.
--grid6=FILE: six-good agents take the grid types of FILE (typesk.py; a subset of all strict types, so 'certified'
             then covers that subset only; a FAIL is a genuine counterexample).
--exact6: with --grid6, every grid cut is confirmed by the exact LP (ratlp.py) and bits the grid misses get the LP's
             point, so 'certified' covers every strict profile (kcegar_exact_check.py validates this).
--rf: test Conjecture RF instead (rfcegar.py; D is ignored): every receiver-first maximum-matching order of every
             failing maximum-matching start satisfies OC1, for every strict profile.
--rfe: the weak form RF-exists (rfcegar.RFE): some receiver-first order gives maximum-matching picks satisfying OC1.
--prio=LOG: (any mode) run first the one-good extensions of the hypergraphs with a FAIL line in LOG.
--ckpt=FILE: append every finished hypergraph's record to FILE (JSON lines) and skip the ones already there (except
             timeouts, which are tried again), so a run can be resumed after the container is reclaimed.
A FAIL is re-checked on its integer representative by ocsat (SAT; empty passes allowed) for D <= 1, by ocseq (SAT, D
chains) and by brute force (every state of up to D chains from the definition, raw-EFX0 backtracking completions)."""
import os, sys, json, time, collections, itertools, multiprocessing as mp
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
import _paths
import kcegar, k3max, brute, ocsat, ocseq


def named():
    import fam_ladder, refute_rd_k5 as RD
    from round_known import KGEN
    from refute_oc1max_k4 import CEX
    out = [('RD5', RD.SETS), ('PW5', fam_ladder.clean(3, 2, 4)[0]), ('kgen-n4', KGEN[0])]
    for c, (S, V, P) in enumerate(CEX):        # each k = 4 counterexample with one agent extended to five goods
        m = 1 + max(max(s) for s in S)
        for i in range(len(S)):
            if len(S[i]) == 4:
                out.append(('cex%d+new@%d' % (c + 1, i), [s + [m] if j == i else s for j, s in enumerate(S)]))
                other = [g for g in range(m) if g not in S[i]]
                if other: out.append(('cex%d+%d@%d' % (c + 1, other[0], i), [s + [other[0]] if j == i else s for j, s in enumerate(S)]))
                break
    return out


def named6():
    """k = 6 hypergraphs built from the known two-chain instances: an agent extended by one or two goods (new goods
    or goods of the instance)"""
    import refute_rd_k5 as RD
    from round_known import KGEN
    from refute_oc1max_k4 import CEX
    from refute_oc1_k5_n3 import SETS as N3
    out = []
    def ext(name, S, i, extra):
        T = [sorted(set(s) | set(extra)) if j == i else list(s) for j, s in enumerate(S)]
        if max(map(len, T)) == 6: out.append((name, T))
    m = lambda S: 1 + max(max(s) for s in S)
    for nm, S in [('RD5', RD.SETS), ('kgen-n4', KGEN[0]), ('N3K5', N3)]:
        for i, s in enumerate(S):
            if len(s) == 5:
                ext('%s+new@%d' % (nm, i), S, i, [m(S)])
                other = [g for g in range(m(S)) if g not in s]
                if other: ext('%s+%d@%d' % (nm, other[0], i), S, i, [other[0]])
    for c, (S, V, P) in enumerate(CEX[:4]):
        for i, s in enumerate(S):
            if len(s) == 4:
                ext('cex%d+2new@%d' % (c + 1, i), S, i, [m(S), m(S) + 1])
                other = [g for g in range(m(S)) if g not in s]
                if len(other) >= 2: ext('cex%d+%d,%d@%d' % (c + 1, other[0], other[1], i), S, i, other[:2])
                break
    return out


def canon(S):
    """isomorphism class of a hypergraph (agents and goods relabelled): the multiset of the goods' agent sets, minimized
    over agent permutations (goods with the same agent set are interchangeable, so this is complete)"""
    n = len(S); goods = sorted(set(g for s in S for g in s))
    return min(tuple(sorted(tuple(sorted(p.index(i) for i in range(n) if g in S[i])) for g in goods))
               for p in map(list, itertools.permutations(range(n))))


def extensions(S):
    """every hypergraph obtained by giving one agent one more good (a new good, or a good it does not value)"""
    m = 1 + max(max(s) for s in S)
    for i, s in enumerate(S):
        for g in [x for x in range(m) if x not in s] + [m]:
            yield [sorted(set(t) | {g}) if j == i else list(t) for j, t in enumerate(S)]


def recheck(R, vals, Y, D, A=1):
    n = len(R); m = 1 + max(max(s) for s in R); vl = [[vals[i][g] for g in R[i]] for i in range(n)]
    V = [[0] * m for _ in range(n)]
    for i in range(n):
        for g, x in vals[i].items(): V[i][g] = x
    base = [frozenset([g]) if g is not None else frozenset() for g in Y]; I = brute.Inst(R, vl, m)
    states = {tuple(base)}; frontier = {tuple(base)}
    for d in range(D):
        frontier = set(s2 for s in frontier for s2 in I.chains(list(s))) - states; states |= frontier
    bf = any(k3max.find_completion(V, s, m, A) is not None for s in states)
    Q = ocseq.Seq(R, vl, m); sq = Q.holds(ocsat.bases_of(Y, n), D, A); Q.close()
    return {'vals': vl, 'picks': Y, 'brute (empty passes allowed) repairs within D': bf, 'ocseq repairs within D': sq,
            'states': len(states)}


def job(task):
    name, sets, D, limit = task; t0 = time.time()
    g6 = next((a[8:] for a in sys.argv if a.startswith('--grid6=')), None)
    ex = '--exact6' in sys.argv; rf = '--rf' in sys.argv or '--rfe' in sys.argv; rfe = '--rfe' in sys.argv
    if rf:
        import rfcegar
        C = (rfcegar.RFE if rfe else rfcegar.RF)(sets, grid6=g6, grid_exact=ex)
    else: C = kcegar.Cegar(sets, D=D, require_max='--any-start' not in sys.argv, grid6=g6, grid_exact=ex)
    r, w = C.run(time_limit=limit); rec = {'name': name, 'sets': sets, 'D': ('RFE' if rfe else 'RF') if rf else D, 'result': r,
        'iterations': C.iters, 'kinds': dict(C.kinds), 'types': [len(t) if t is not None else ('grid' if C.G[i] else 'LP') for i, t in enumerate(C.T)],
        'grid6': g6, 'exact6': ex, 'grid_stats': dict(C.gstats),
        'lp_calls': C.lpcalls}
    if r == 'FAIL': rec['recheck'] = (rfcegar.recheck_e(C.R, *w) if rfe else rfcegar.recheck(C.R, *w)) if rf else recheck(C.R, w[0], w[1], D)
    C.close(); rec['time'] = round(time.time() - t0, 1); return rec


if __name__ == '__main__':
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[1:] if a.startswith('--') and '=' in a)
    jobs = int(opt.get('jobs', 4)); limit = float(opt['limit']) if 'limit' in opt else None
    print('$ python3 k4/ksens/kcegar_batch.py', *sys.argv[1:], flush=True); t0 = time.time()
    if args[0] == 'genbg':
        n, k, D = map(int, args[1:4]); ms = [int(a) for a in args[4:]] or list(range(n, k * n + 1))
        import subprocess, networkx as nx
        tasks = []
        for m in ms:
            out = subprocess.run(['nauty-genbg', '-c', '-q', '-d1:1', '-D%d:%d' % (k, n), str(n), str(m)], capture_output=True).stdout.split()
            kmin = int(opt.get('kmin', 0))
            for idx, line in enumerate(out):
                G = nx.from_graph6_bytes(line); sets = [sorted(g - n for g in G[i]) for i in range(n)]
                if max(map(len, sets)) >= kmin: tasks.append(('n%d_m%d_%d' % (n, m, idx), sets, D, limit))
    elif args[0] in ('core5', 'core'):
        if args[0] == 'core5': n, D = map(int, args[1:3]); K = 5; ms = [int(a) for a in args[3:]]
        else: n, K, D = map(int, args[1:4]); ms = [int(a) for a in args[4:]]
        ms = ms or list(range(n, K * n + 1))
        import subprocess, networkx as nx
        tasks = []
        for m in ms:
            out = subprocess.run(['nauty-genbg', '-c', '-q', '-d3:1', '-D%d:%d' % (K, n), str(n), str(m)], capture_output=True).stdout.split()
            for idx, line in enumerate(out):
                G = nx.from_graph6_bytes(line); sets = [sorted(g - n for g in G[i]) for i in range(n)]
                if max(map(len, sets)) < K: continue
                deg = {g: sum(g in x for x in sets) for g in range(m)}
                if any(sum(deg[g] == 1 for g in x) > len(x) - 2 for x in sets): continue
                tasks.append(('core%d_n%d_m%d_%d' % (K, n, m, idx), sets, D, limit))
    elif args[0] == 'named6':
        D = int(args[1]); tasks = [(nm, s, D, limit) for nm, s in named6()]
    else:
        D = int(args[1]); tasks = [(nm, s, D, limit) for nm, s in named()]
    if 'prio' in opt:
        # run first the hypergraphs that are one-good extensions of a hypergraph with a FAIL line in the given log
        # (e.g. the k = 5, D = 1 failures for a k = 6, D = 2 sweep); the set of tasks is unchanged, only the order
        prio = set()
        for l in open(opt['prio']):
            if '"result": "FAIL"' not in l: continue
            S = json.loads(l)['sets']
            for H in extensions(S): prio.add(canon(H))
        key = {t[0]: (canon(t[1]) not in prio) for t in tasks}
        tasks.sort(key=lambda t: key[t[0]])
        print('priority (one-good extensions of the FAIL hypergraphs of %s): %d of %d tasks first' % (
            opt['prio'], sum(not v for v in key.values()), len(tasks)), flush=True)
    C = collections.Counter(); ck = opt.get('ckpt')
    if ck:
        import os
        done = {}
        if os.path.exists(ck):
            for l in open(ck):
                try: r = json.loads(l)
                except Exception: continue
                if r['result'] != 'timeout': done[r['name']] = r['result']       # a timeout is tried again
        for r in done.values(): C[r] += 1
        tasks = [t for t in tasks if t[0] not in done]; ckf = open(ck, 'a')
        print('checkpoint %s: %d done (%s), %d to go' % (ck, len(done), dict(C), len(tasks)), flush=True)
    print('hypergraphs', len(tasks), flush=True)
    with mp.Pool(jobs) as P:
        for rec in P.imap_unordered(job, tasks, chunksize=1):
            C[rec['result']] += 1
            if ck: ckf.write(json.dumps(rec) + '\n'); ckf.flush()
            if rec['result'] != 'certified' or args[0] in ('named', 'named6'): print(json.dumps(rec), flush=True)
            if sum(C.values()) % 100 == 0: print('...', sum(C.values()), dict(C), '%.0f s' % (time.time() - t0), flush=True)
    print(dict(C), 'time %.0f s' % (time.time() - t0))
