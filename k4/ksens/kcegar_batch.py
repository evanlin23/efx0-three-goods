"""Batch runner for kcegar.py (k4/ksens.md §8): OC_D^max for every strict profile of every hypergraph in a list.

    python3 k4/ksens/kcegar_batch.py genbg n k D [m ...] [--jobs=4] [--limit=SEC]    every connected hypergraph with n
                                                                                      agents, each valuing <= k goods
    python3 k4/ksens/kcegar_batch.py named D [--jobs=4] [--limit=SEC]                 the k = 5 list NAMED below
A FAIL is re-checked on its integer representative by ocsat (SAT; empty passes allowed) for D <= 1, by ocseq (SAT, D
chains) and by brute force (every state of up to D chains from the definition, raw-EFX0 backtracking completions)."""
import sys, json, time, collections, multiprocessing as mp
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
    C = kcegar.Cegar(sets, D=D); r, w = C.run(time_limit=limit); rec = {'name': name, 'sets': sets, 'D': D, 'result': r,
        'iterations': C.iters, 'kinds': dict(C.kinds), 'types': [len(t) for t in C.T]}
    if r == 'FAIL': rec['recheck'] = recheck(C.R, w[0], w[1], D)
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
            for idx, line in enumerate(out):
                G = nx.from_graph6_bytes(line); tasks.append(('n%d_m%d_%d' % (n, m, idx), [sorted(g - n for g in G[i]) for i in range(n)], D, limit))
    else:
        D = int(args[1]); tasks = [(nm, s, D, limit) for nm, s in named()]
    print('hypergraphs', len(tasks), flush=True); C = collections.Counter()
    with mp.Pool(jobs) as P:
        for rec in P.imap_unordered(job, tasks, chunksize=1):
            C[rec['result']] += 1
            if rec['result'] != 'certified' or args[0] != 'genbg': print(json.dumps(rec), flush=True)
    print(dict(C), 'time %.0f s' % (time.time() - t0))
