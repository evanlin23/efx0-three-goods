"""Class U0 (k4/rkmax.md §6): is the sigma-raise local?  At each U0 residue start (one receiver z, Theta(z) = {k},
D_T empty, hard, no Lemma S'), let L = {k, z} + the agents of the longest canonical chains from k.  Is there a maximum
matching with larger sigma that differs from Y only on L?  If not, a proof of HS-MAX in U0 cannot be local to the
S' failure.
    python3 rk_u0_local.py STRIDE"""
import sys, os, gzip, json, collections, multiprocessing as mp
from rklib import Prof
from rk_classes import theta, sprime_cases

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')


def job(task):
    sets, vals = task
    P = Prof(sets, vals); n = P.n; nu, mm = P.max_matchings(); C = collections.Counter(); ex = []
    for Y in mm:
        if not P.pareto_optimal(Y): continue
        ro = P.roles(Y)
        if len(ro['U']) != 1 or ro['DT']: continue
        z = ro['U'][0]; th = theta(P, Y, ro, z)
        if len(th) != 1: continue
        if P.one_absorber([frozenset([g]) for g in Y]) is not None or sprime_cases(P, Y, ro): continue
        k = th[0]; W = ro['wants']; chains = []
        def ext(path):
            x = path[-1]
            if len(path) >= 2 and x == z: chains.append(path); return
            for y in range(n):
                if y not in path and (y, x) in W: ext(path + [y])
        ext([k]); Lmax = max(len(c) for c in chains)
        L = {k, z} | {a for c in chains if len(c) == Lmax for a in c}
        sY = P.sigma(Y)
        loc = any(P.sigma(M) > sY and all(M[i] == Y[i] for i in range(n) if i not in L) for M in mm)
        kz = any(P.sigma(M) > sY and all(M[i] == Y[i] for i in range(n) if i not in (k, z)) for M in mm)
        C['U0 residue start'] += 1
        C['  sigma-raise inside {k, z}: %s' % kz] += 1
        C['  sigma-raise inside {k, z} + longest chains: %s' % loc] += 1
        C['  longest chain length %d' % (Lmax - 1)] += 1
        if not loc and len(ex) < 2: ex.append({'sets': sets, 'vals': vals, 'picks': Y, 'k': k, 'z': z})
    return C, ex


if __name__ == '__main__':
    STRIDE = int(sys.argv[1])
    print('$ python3 k4/rkmax/rk_u0_local.py', STRIDE, flush=True)
    d = json.load(gzip.open(os.path.join(ROOT, 'results', 'k4_oc1max', 'two_move_starts_n4.json.gz'))); prof = {}
    for h in d['hypergraphs']:
        for st in h['starts']: prof[(json.dumps(h['sets']), json.dumps(st['vals']))] = (h['sets'], st['vals'])
    T = collections.Counter(); shown = 0
    with mp.Pool(2) as pool:
        for C, ex in pool.imap_unordered(job, list(prof.values())[::STRIDE], chunksize=4):
            T.update(C)
            for e in ex:
                if shown < 3: shown += 1; print('NONLOCAL', json.dumps(e), flush=True)
    for k in sorted(T): print(k, T[k])
